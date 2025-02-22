//===- Writer.cpp ---------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "Writer.h"
#include "AArch64ErrataFix.h"
#include "CallGraphSort.h"
#include "Config.h"
#include "LinkerScript.h"
#include "MapFile.h"
#include "OutputSections.h"
#include "Relocations.h"
#include "SymbolTable.h"
#include "Symbols.h"
#include "SyntheticSections.h"
#include "Target.h"
#include "lld/Common/Filesystem.h"
#include "lld/Common/Memory.h"
#include "lld/Common/Strings.h"
#include "lld/Common/Threads.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/RandomNumberGenerator.h"
#include "llvm/Support/SHA1.h"
#include "llvm/Support/xxhash.h"
#include <climits>

using namespace llvm;
using namespace llvm::ELF;
using namespace llvm::object;
using namespace llvm::support;
using namespace llvm::support::endian;

using namespace lld;
using namespace lld::elf;

namespace {
// The writer writes a SymbolTable result to a file.
template <class ELFT> class Writer {
public:
  Writer() : Buffer(errorHandler().OutputBuffer) {}
  using Elf_Shdr = typename ELFT::Shdr;
  using Elf_Ehdr = typename ELFT::Ehdr;
  using Elf_Phdr = typename ELFT::Phdr;

  void run();

private:
  void copyLocalSymbols();
  void addSectionSymbols();
  void forEachRelSec(llvm::function_ref<void(InputSectionBase &)> Fn);
  void sortSections();
  void resolveShfLinkOrder();
  void finalizeAddressDependentContent();
  void sortInputSections();
  void finalizeSections();
  void checkExecuteOnly();
  void setReservedSymbolSections();

  std::vector<PhdrEntry *> createPhdrs(Partition &Part);
  void removeEmptyPTLoad(std::vector<PhdrEntry *> &PhdrEntry);
  void addPhdrForSection(Partition &Part, unsigned ShType, unsigned PType,
                         unsigned PFlags);
  void assignFileOffsets();
  void assignFileOffsetsBinary();
  void setPhdrs(Partition &Part);
  void checkSections();
  void fixSectionAlignments();
  void openFile();
  void writeTrapInstr();
  void writeHeader();
  void writeSections();
  void writeSectionsBinary();
  void writeBuildId();

  std::unique_ptr<FileOutputBuffer> &Buffer;

  void addRelIpltSymbols();
  void addStartEndSymbols();
  void addStartStopSymbols(OutputSection *Sec);

  uint64_t FileSize;
  uint64_t SectionHeaderOff;
};
} // anonymous namespace

static bool isSectionPrefix(StringRef Prefix, StringRef Name) {
  return Name.startswith(Prefix) || Name == Prefix.drop_back();
}

StringRef elf::getOutputSectionName(const InputSectionBase *S) {
  if (Config->Relocatable)
    return S->Name;

  // This is for --emit-relocs. If .text.foo is emitted as .text.bar, we want
  // to emit .rela.text.foo as .rela.text.bar for consistency (this is not
  // technically required, but not doing it is odd). This code guarantees that.
  if (auto *IS = dyn_cast<InputSection>(S)) {
    if (InputSectionBase *Rel = IS->getRelocatedSection()) {
      OutputSection *Out = Rel->getOutputSection();
      if (S->Type == SHT_RELA)
        return Saver.save(".rela" + Out->Name);
      return Saver.save(".rel" + Out->Name);
    }
  }

  // This check is for -z keep-text-section-prefix.  This option separates text
  // sections with prefix ".text.hot", ".text.unlikely", ".text.startup" or
  // ".text.exit".
  // When enabled, this allows identifying the hot code region (.text.hot) in
  // the final binary which can be selectively mapped to huge pages or mlocked,
  // for instance.
  if (Config->ZKeepTextSectionPrefix)
    for (StringRef V :
         {".text.hot.", ".text.unlikely.", ".text.startup.", ".text.exit."})
      if (isSectionPrefix(V, S->Name))
        return V.drop_back();

  for (StringRef V :
       {".text.", ".rodata.", ".data.rel.ro.", ".data.", ".bss.rel.ro.",
        ".bss.", ".init_array.", ".fini_array.", ".ctors.", ".dtors.", ".tbss.",
        ".gcc_except_table.", ".tdata.", ".ARM.exidx.", ".ARM.extab."})
    if (isSectionPrefix(V, S->Name))
      return V.drop_back();

  // CommonSection is identified as "COMMON" in linker scripts.
  // By default, it should go to .bss section.
  if (S->Name == "COMMON")
    return ".bss";

  return S->Name;
}

static bool needsInterpSection() {
  return !SharedFiles.empty() && !Config->DynamicLinker.empty() &&
         Script->needsInterpSection();
}

template <class ELFT> void elf::writeResult() { Writer<ELFT>().run(); }

template <class ELFT>
void Writer<ELFT>::removeEmptyPTLoad(std::vector<PhdrEntry *> &Phdrs) {
  llvm::erase_if(Phdrs, [&](const PhdrEntry *P) {
    if (P->p_type != PT_LOAD)
      return false;
    if (!P->FirstSec)
      return true;
    uint64_t Size = P->LastSec->Addr + P->LastSec->Size - P->FirstSec->Addr;
    return Size == 0;
  });
}

template <class ELFT> static void copySectionsIntoPartitions() {
  std::vector<InputSectionBase *> NewSections;
  for (unsigned Part = 2; Part != Partitions.size() + 1; ++Part) {
    for (InputSectionBase *S : InputSections) {
      if (!(S->Flags & SHF_ALLOC) || !S->isLive())
        continue;
      InputSectionBase *Copy;
      if (S->Type == SHT_NOTE)
        Copy = make<InputSection>(cast<InputSection>(*S));
      else if (auto *ES = dyn_cast<EhInputSection>(S))
        Copy = make<EhInputSection>(*ES);
      else
        continue;
      Copy->Partition = Part;
      NewSections.push_back(Copy);
    }
  }

  InputSections.insert(InputSections.end(), NewSections.begin(),
                       NewSections.end());
}

template <class ELFT> static void combineEhSections() {
  for (InputSectionBase *&S : InputSections) {
    // Ignore dead sections and the partition end marker (.part.end),
    // whose partition number is out of bounds.
    if (!S->isLive() || S->Partition == 255)
      continue;

    Partition &Part = S->getPartition();
    if (auto *ES = dyn_cast<EhInputSection>(S)) {
      Part.EhFrame->addSection<ELFT>(ES);
      S = nullptr;
    } else if (S->kind() == SectionBase::Regular && Part.ARMExidx &&
               Part.ARMExidx->addSection(cast<InputSection>(S))) {
      S = nullptr;
    }
  }

  std::vector<InputSectionBase *> &V = InputSections;
  V.erase(std::remove(V.begin(), V.end(), nullptr), V.end());
}

static Defined *addOptionalRegular(StringRef Name, SectionBase *Sec,
                                   uint64_t Val, uint8_t StOther = STV_HIDDEN,
                                   uint8_t Binding = STB_GLOBAL) {
  Symbol *S = Symtab->find(Name);
  if (!S || S->isDefined())
    return nullptr;

  S->resolve(Defined{/*File=*/nullptr, Name, Binding, StOther, STT_NOTYPE, Val,
                     /*Size=*/0, Sec});
  return cast<Defined>(S);
}

static Defined *addAbsolute(StringRef Name) {
  Symbol *Sym = Symtab->addSymbol(Defined{nullptr, Name, STB_GLOBAL, STV_HIDDEN,
                                          STT_NOTYPE, 0, 0, nullptr});
  return cast<Defined>(Sym);
}

// The linker is expected to define some symbols depending on
// the linking result. This function defines such symbols.
void elf::addReservedSymbols() {
  if (Config->EMachine == EM_MIPS) {
    // Define _gp for MIPS. st_value of _gp symbol will be updated by Writer
    // so that it points to an absolute address which by default is relative
    // to GOT. Default offset is 0x7ff0.
    // See "Global Data Symbols" in Chapter 6 in the following document:
    // ftp://www.linux-mips.org/pub/linux/mips/doc/ABI/mipsabi.pdf
    ElfSym::MipsGp = addAbsolute("_gp");

    // On MIPS O32 ABI, _gp_disp is a magic symbol designates offset between
    // start of function and 'gp' pointer into GOT.
    if (Symtab->find("_gp_disp"))
      ElfSym::MipsGpDisp = addAbsolute("_gp_disp");

    // The __gnu_local_gp is a magic symbol equal to the current value of 'gp'
    // pointer. This symbol is used in the code generated by .cpload pseudo-op
    // in case of using -mno-shared option.
    // https://sourceware.org/ml/binutils/2004-12/msg00094.html
    if (Symtab->find("__gnu_local_gp"))
      ElfSym::MipsLocalGp = addAbsolute("__gnu_local_gp");
  } else if (Config->EMachine == EM_PPC) {
    // glibc *crt1.o has a undefined reference to _SDA_BASE_. Since we don't
    // support Small Data Area, define it arbitrarily as 0.
    addOptionalRegular("_SDA_BASE_", nullptr, 0, STV_HIDDEN);
  }

  // The Power Architecture 64-bit v2 ABI defines a TableOfContents (TOC) which
  // combines the typical ELF GOT with the small data sections. It commonly
  // includes .got .toc .sdata .sbss. The .TOC. symbol replaces both
  // _GLOBAL_OFFSET_TABLE_ and _SDA_BASE_ from the 32-bit ABI. It is used to
  // represent the TOC base which is offset by 0x8000 bytes from the start of
  // the .got section.
  // We do not allow _GLOBAL_OFFSET_TABLE_ to be defined by input objects as the
  // correctness of some relocations depends on its value.
  StringRef GotSymName =
      (Config->EMachine == EM_PPC64) ? ".TOC." : "_GLOBAL_OFFSET_TABLE_";

  if (Symbol *S = Symtab->find(GotSymName)) {
    if (S->isDefined()) {
      error(toString(S->File) + " cannot redefine linker defined symbol '" +
            GotSymName + "'");
      return;
    }

    uint64_t GotOff = 0;
    if (Config->EMachine == EM_PPC64)
      GotOff = 0x8000;

    S->resolve(Defined{/*File=*/nullptr, GotSymName, STB_GLOBAL, STV_HIDDEN,
                       STT_NOTYPE, GotOff, /*Size=*/0, Out::ElfHeader});
    ElfSym::GlobalOffsetTable = cast<Defined>(S);
  }

  // __ehdr_start is the location of ELF file headers. Note that we define
  // this symbol unconditionally even when using a linker script, which
  // differs from the behavior implemented by GNU linker which only define
  // this symbol if ELF headers are in the memory mapped segment.
  addOptionalRegular("__ehdr_start", Out::ElfHeader, 0, STV_HIDDEN);

  // __executable_start is not documented, but the expectation of at
  // least the Android libc is that it points to the ELF header.
  addOptionalRegular("__executable_start", Out::ElfHeader, 0, STV_HIDDEN);

  // __dso_handle symbol is passed to cxa_finalize as a marker to identify
  // each DSO. The address of the symbol doesn't matter as long as they are
  // different in different DSOs, so we chose the start address of the DSO.
  addOptionalRegular("__dso_handle", Out::ElfHeader, 0, STV_HIDDEN);

  // If linker script do layout we do not need to create any standart symbols.
  if (Script->HasSectionsCommand)
    return;

  auto Add = [](StringRef S, int64_t Pos) {
    return addOptionalRegular(S, Out::ElfHeader, Pos, STV_DEFAULT);
  };

  ElfSym::Bss = Add("__bss_start", 0);
  ElfSym::End1 = Add("end", -1);
  ElfSym::End2 = Add("_end", -1);
  ElfSym::Etext1 = Add("etext", -1);
  ElfSym::Etext2 = Add("_etext", -1);
  ElfSym::Edata1 = Add("edata", -1);
  ElfSym::Edata2 = Add("_edata", -1);
}

static OutputSection *findSection(StringRef Name, unsigned Partition = 1) {
  for (BaseCommand *Base : Script->SectionCommands)
    if (auto *Sec = dyn_cast<OutputSection>(Base))
      if (Sec->Name == Name && Sec->Partition == Partition)
        return Sec;
  return nullptr;
}

// Initialize Out members.
template <class ELFT> static void createSyntheticSections() {
  // Initialize all pointers with NULL. This is needed because
  // you can call lld::elf::main more than once as a library.
  memset(&Out::First, 0, sizeof(Out));

  auto Add = [](InputSectionBase *Sec) { InputSections.push_back(Sec); };

  In.ShStrTab = make<StringTableSection>(".shstrtab", false);

  Out::ProgramHeaders = make<OutputSection>("", 0, SHF_ALLOC);
  Out::ProgramHeaders->Alignment = Config->Wordsize;

  if (Config->Strip != StripPolicy::All) {
    In.StrTab = make<StringTableSection>(".strtab", false);
    In.SymTab = make<SymbolTableSection<ELFT>>(*In.StrTab);
    In.SymTabShndx = make<SymtabShndxSection>();
  }

  In.Bss = make<BssSection>(".bss", 0, 1);
  Add(In.Bss);

  // If there is a SECTIONS command and a .data.rel.ro section name use name
  // .data.rel.ro.bss so that we match in the .data.rel.ro output section.
  // This makes sure our relro is contiguous.
  bool HasDataRelRo =
      Script->HasSectionsCommand && findSection(".data.rel.ro", 0);
  In.BssRelRo =
      make<BssSection>(HasDataRelRo ? ".data.rel.ro.bss" : ".bss.rel.ro", 0, 1);
  Add(In.BssRelRo);

  // Add MIPS-specific sections.
  if (Config->EMachine == EM_MIPS) {
    if (!Config->Shared && Config->HasDynSymTab) {
      In.MipsRldMap = make<MipsRldMapSection>();
      Add(In.MipsRldMap);
    }
    if (auto *Sec = MipsAbiFlagsSection<ELFT>::create())
      Add(Sec);
    if (auto *Sec = MipsOptionsSection<ELFT>::create())
      Add(Sec);
    if (auto *Sec = MipsReginfoSection<ELFT>::create())
      Add(Sec);
  }

  for (Partition &Part : Partitions) {
    auto Add = [&](InputSectionBase *Sec) {
      Sec->Partition = Part.getNumber();
      InputSections.push_back(Sec);
    };

    if (!Part.Name.empty()) {
      Part.ElfHeader = make<PartitionElfHeaderSection<ELFT>>();
      Part.ElfHeader->Name = Part.Name;
      Add(Part.ElfHeader);

      Part.ProgramHeaders = make<PartitionProgramHeadersSection<ELFT>>();
      Add(Part.ProgramHeaders);
    }

    if (Config->BuildId != BuildIdKind::None) {
      Part.BuildId = make<BuildIdSection>();
      Add(Part.BuildId);
    }

    Part.DynStrTab = make<StringTableSection>(".dynstr", true);
    Part.DynSymTab = make<SymbolTableSection<ELFT>>(*Part.DynStrTab);
    Part.Dynamic = make<DynamicSection<ELFT>>();
    if (Config->AndroidPackDynRelocs) {
      Part.RelaDyn = make<AndroidPackedRelocationSection<ELFT>>(
          Config->IsRela ? ".rela.dyn" : ".rel.dyn");
    } else {
      Part.RelaDyn = make<RelocationSection<ELFT>>(
          Config->IsRela ? ".rela.dyn" : ".rel.dyn", Config->ZCombreloc);
    }

    if (needsInterpSection())
      Add(createInterpSection());

    if (Config->HasDynSymTab) {
      Part.DynSymTab = make<SymbolTableSection<ELFT>>(*Part.DynStrTab);
      Add(Part.DynSymTab);

      Part.VerSym = make<VersionTableSection>();
      Add(Part.VerSym);

      if (!Config->VersionDefinitions.empty()) {
        Part.VerDef = make<VersionDefinitionSection>();
        Add(Part.VerDef);
      }

      Part.VerNeed = make<VersionNeedSection<ELFT>>();
      Add(Part.VerNeed);

      if (Config->GnuHash) {
        Part.GnuHashTab = make<GnuHashTableSection>();
        Add(Part.GnuHashTab);
      }

      if (Config->SysvHash) {
        Part.HashTab = make<HashTableSection>();
        Add(Part.HashTab);
      }

      Add(Part.Dynamic);
      Add(Part.DynStrTab);
      Add(Part.RelaDyn);
    }

    if (Config->RelrPackDynRelocs) {
      Part.RelrDyn = make<RelrSection<ELFT>>();
      Add(Part.RelrDyn);
    }

    if (!Config->Relocatable) {
      if (Config->EhFrameHdr) {
        Part.EhFrameHdr = make<EhFrameHeader>();
        Add(Part.EhFrameHdr);
      }
      Part.EhFrame = make<EhFrameSection>();
      Add(Part.EhFrame);
    }

    if (Config->EMachine == EM_ARM && !Config->Relocatable) {
      // The ARMExidxsyntheticsection replaces all the individual .ARM.exidx
      // InputSections.
      Part.ARMExidx = make<ARMExidxSyntheticSection>();
      Add(Part.ARMExidx);
    }
  }

  if (Partitions.size() != 1) {
    // Create the partition end marker. This needs to be in partition number 255
    // so that it is sorted after all other partitions. It also has other
    // special handling (see createPhdrs() and combineEhSections()).
    In.PartEnd = make<BssSection>(".part.end", Config->MaxPageSize, 1);
    In.PartEnd->Partition = 255;
    Add(In.PartEnd);

    In.PartIndex = make<PartitionIndexSection>();
    addOptionalRegular("__part_index_begin", In.PartIndex, 0);
    addOptionalRegular("__part_index_end", In.PartIndex,
                       In.PartIndex->getSize());
    Add(In.PartIndex);
  }

  // Add .got. MIPS' .got is so different from the other archs,
  // it has its own class.
  if (Config->EMachine == EM_MIPS) {
    In.MipsGot = make<MipsGotSection>();
    Add(In.MipsGot);
  } else {
    In.Got = make<GotSection>();
    Add(In.Got);
  }

  if (Config->EMachine == EM_PPC) {
    In.PPC32Got2 = make<PPC32Got2Section>();
    Add(In.PPC32Got2);
  }

  if (Config->EMachine == EM_PPC64) {
    In.PPC64LongBranchTarget = make<PPC64LongBranchTargetSection>();
    Add(In.PPC64LongBranchTarget);
  }

  In.GotPlt = make<GotPltSection>();
  Add(In.GotPlt);
  In.IgotPlt = make<IgotPltSection>();
  Add(In.IgotPlt);

  // _GLOBAL_OFFSET_TABLE_ is defined relative to either .got.plt or .got. Treat
  // it as a relocation and ensure the referenced section is created.
  if (ElfSym::GlobalOffsetTable && Config->EMachine != EM_MIPS) {
    if (Target->GotBaseSymInGotPlt)
      In.GotPlt->HasGotPltOffRel = true;
    else
      In.Got->HasGotOffRel = true;
  }

  if (Config->GdbIndex)
    Add(GdbIndexSection::create<ELFT>());

  // We always need to add rel[a].plt to output if it has entries.
  // Even for static linking it can contain R_[*]_IRELATIVE relocations.
  In.RelaPlt = make<RelocationSection<ELFT>>(
      Config->IsRela ? ".rela.plt" : ".rel.plt", false /*Sort*/);
  Add(In.RelaPlt);

  // The RelaIplt immediately follows .rel.plt (.rel.dyn for ARM) to ensure
  // that the IRelative relocations are processed last by the dynamic loader.
  // We cannot place the iplt section in .rel.dyn when Android relocation
  // packing is enabled because that would cause a section type mismatch.
  // However, because the Android dynamic loader reads .rel.plt after .rel.dyn,
  // we can get the desired behaviour by placing the iplt section in .rel.plt.
  In.RelaIplt = make<RelocationSection<ELFT>>(
      (Config->EMachine == EM_ARM && !Config->AndroidPackDynRelocs)
          ? ".rel.dyn"
          : In.RelaPlt->Name,
      false /*Sort*/);
  Add(In.RelaIplt);

  In.Plt = make<PltSection>(false);
  Add(In.Plt);
  In.Iplt = make<PltSection>(true);
  Add(In.Iplt);

  if (Config->AndFeatures)
    Add(make<GnuPropertySection>());

  // .note.GNU-stack is always added when we are creating a re-linkable
  // object file. Other linkers are using the presence of this marker
  // section to control the executable-ness of the stack area, but that
  // is irrelevant these days. Stack area should always be non-executable
  // by default. So we emit this section unconditionally.
  if (Config->Relocatable)
    Add(make<GnuStackSection>());

  if (In.SymTab)
    Add(In.SymTab);
  if (In.SymTabShndx)
    Add(In.SymTabShndx);
  Add(In.ShStrTab);
  if (In.StrTab)
    Add(In.StrTab);
}

// The main function of the writer.
template <class ELFT> void Writer<ELFT>::run() {
  // Make copies of any input sections that need to be copied into each
  // partition.
  copySectionsIntoPartitions<ELFT>();

  // Create linker-synthesized sections such as .got or .plt.
  // Such sections are of type input section.
  createSyntheticSections<ELFT>();

  // Some input sections that are used for exception handling need to be moved
  // into synthetic sections. Do that now so that they aren't assigned to
  // output sections in the usual way.
  if (!Config->Relocatable)
    combineEhSections<ELFT>();

  // We want to process linker script commands. When SECTIONS command
  // is given we let it create sections.
  Script->processSectionCommands();

  // Linker scripts controls how input sections are assigned to output sections.
  // Input sections that were not handled by scripts are called "orphans", and
  // they are assigned to output sections by the default rule. Process that.
  Script->addOrphanSections();

  if (Config->Discard != DiscardPolicy::All)
    copyLocalSymbols();

  if (Config->CopyRelocs)
    addSectionSymbols();

  // Now that we have a complete set of output sections. This function
  // completes section contents. For example, we need to add strings
  // to the string table, and add entries to .got and .plt.
  // finalizeSections does that.
  finalizeSections();
  checkExecuteOnly();
  if (errorCount())
    return;

  Script->assignAddresses();

  // If -compressed-debug-sections is specified, we need to compress
  // .debug_* sections. Do it right now because it changes the size of
  // output sections.
  for (OutputSection *Sec : OutputSections)
    Sec->maybeCompress<ELFT>();

  Script->allocateHeaders(Main->Phdrs);

  // Remove empty PT_LOAD to avoid causing the dynamic linker to try to mmap a
  // 0 sized region. This has to be done late since only after assignAddresses
  // we know the size of the sections.
  for (Partition &Part : Partitions)
    removeEmptyPTLoad(Part.Phdrs);

  if (!Config->OFormatBinary)
    assignFileOffsets();
  else
    assignFileOffsetsBinary();

  for (Partition &Part : Partitions)
    setPhdrs(Part);

  if (Config->Relocatable)
    for (OutputSection *Sec : OutputSections)
      Sec->Addr = 0;

  if (Config->CheckSections)
    checkSections();

  // It does not make sense try to open the file if we have error already.
  if (errorCount())
    return;
  // Write the result down to a file.
  openFile();
  if (errorCount())
    return;

  if (!Config->OFormatBinary) {
    writeTrapInstr();
    writeHeader();
    writeSections();
  } else {
    writeSectionsBinary();
  }

  // Backfill .note.gnu.build-id section content. This is done at last
  // because the content is usually a hash value of the entire output file.
  writeBuildId();
  if (errorCount())
    return;

  // Handle -Map and -cref options.
  writeMapFile();
  writeCrossReferenceTable();
  if (errorCount())
    return;

  if (auto E = Buffer->commit())
    error("failed to write to the output file: " + toString(std::move(E)));
}

static bool shouldKeepInSymtab(const Defined &Sym) {
  if (Sym.isSection())
    return false;

  if (Config->Discard == DiscardPolicy::None)
    return true;

  // If -emit-reloc is given, all symbols including local ones need to be
  // copied because they may be referenced by relocations.
  if (Config->EmitRelocs)
    return true;

  // In ELF assembly .L symbols are normally discarded by the assembler.
  // If the assembler fails to do so, the linker discards them if
  // * --discard-locals is used.
  // * The symbol is in a SHF_MERGE section, which is normally the reason for
  //   the assembler keeping the .L symbol.
  StringRef Name = Sym.getName();
  bool IsLocal = Name.startswith(".L") || Name.empty();
  if (!IsLocal)
    return true;

  if (Config->Discard == DiscardPolicy::Locals)
    return false;

  SectionBase *Sec = Sym.Section;
  return !Sec || !(Sec->Flags & SHF_MERGE);
}

static bool includeInSymtab(const Symbol &B) {
  if (!B.isLocal() && !B.IsUsedInRegularObj)
    return false;

  if (auto *D = dyn_cast<Defined>(&B)) {
    // Always include absolute symbols.
    SectionBase *Sec = D->Section;
    if (!Sec)
      return true;
    Sec = Sec->Repl;

    // Exclude symbols pointing to garbage-collected sections.
    if (isa<InputSectionBase>(Sec) && !Sec->isLive())
      return false;

    if (auto *S = dyn_cast<MergeInputSection>(Sec))
      if (!S->getSectionPiece(D->Value)->Live)
        return false;
    return true;
  }
  return B.Used;
}

// Local symbols are not in the linker's symbol table. This function scans
// each object file's symbol table to copy local symbols to the output.
template <class ELFT> void Writer<ELFT>::copyLocalSymbols() {
  if (!In.SymTab)
    return;
  for (InputFile *File : ObjectFiles) {
    ObjFile<ELFT> *F = cast<ObjFile<ELFT>>(File);
    for (Symbol *B : F->getLocalSymbols()) {
      if (!B->isLocal())
        fatal(toString(F) +
              ": broken object: getLocalSymbols returns a non-local symbol");
      auto *DR = dyn_cast<Defined>(B);

      // No reason to keep local undefined symbol in symtab.
      if (!DR)
        continue;
      if (!includeInSymtab(*B))
        continue;
      if (!shouldKeepInSymtab(*DR))
        continue;
      In.SymTab->addSymbol(B);
    }
  }
}

// Create a section symbol for each output section so that we can represent
// relocations that point to the section. If we know that no relocation is
// referring to a section (that happens if the section is a synthetic one), we
// don't create a section symbol for that section.
template <class ELFT> void Writer<ELFT>::addSectionSymbols() {
  for (BaseCommand *Base : Script->SectionCommands) {
    auto *Sec = dyn_cast<OutputSection>(Base);
    if (!Sec)
      continue;
    auto I = llvm::find_if(Sec->SectionCommands, [](BaseCommand *Base) {
      if (auto *ISD = dyn_cast<InputSectionDescription>(Base))
        return !ISD->Sections.empty();
      return false;
    });
    if (I == Sec->SectionCommands.end())
      continue;
    InputSection *IS = cast<InputSectionDescription>(*I)->Sections[0];

    // Relocations are not using REL[A] section symbols.
    if (IS->Type == SHT_REL || IS->Type == SHT_RELA)
      continue;

    // Unlike other synthetic sections, mergeable output sections contain data
    // copied from input sections, and there may be a relocation pointing to its
    // contents if -r or -emit-reloc are given.
    if (isa<SyntheticSection>(IS) && !(IS->Flags & SHF_MERGE))
      continue;

    auto *Sym =
        make<Defined>(IS->File, "", STB_LOCAL, /*StOther=*/0, STT_SECTION,
                      /*Value=*/0, /*Size=*/0, IS);
    In.SymTab->addSymbol(Sym);
  }
}

// Today's loaders have a feature to make segments read-only after
// processing dynamic relocations to enhance security. PT_GNU_RELRO
// is defined for that.
//
// This function returns true if a section needs to be put into a
// PT_GNU_RELRO segment.
static bool isRelroSection(const OutputSection *Sec) {
  if (!Config->ZRelro)
    return false;

  uint64_t Flags = Sec->Flags;

  // Non-allocatable or non-writable sections don't need RELRO because
  // they are not writable or not even mapped to memory in the first place.
  // RELRO is for sections that are essentially read-only but need to
  // be writable only at process startup to allow dynamic linker to
  // apply relocations.
  if (!(Flags & SHF_ALLOC) || !(Flags & SHF_WRITE))
    return false;

  // Once initialized, TLS data segments are used as data templates
  // for a thread-local storage. For each new thread, runtime
  // allocates memory for a TLS and copy templates there. No thread
  // are supposed to use templates directly. Thus, it can be in RELRO.
  if (Flags & SHF_TLS)
    return true;

  // .init_array, .preinit_array and .fini_array contain pointers to
  // functions that are executed on process startup or exit. These
  // pointers are set by the static linker, and they are not expected
  // to change at runtime. But if you are an attacker, you could do
  // interesting things by manipulating pointers in .fini_array, for
  // example. So they are put into RELRO.
  uint32_t Type = Sec->Type;
  if (Type == SHT_INIT_ARRAY || Type == SHT_FINI_ARRAY ||
      Type == SHT_PREINIT_ARRAY)
    return true;

  // .got contains pointers to external symbols. They are resolved by
  // the dynamic linker when a module is loaded into memory, and after
  // that they are not expected to change. So, it can be in RELRO.
  if (In.Got && Sec == In.Got->getParent())
    return true;

  // .toc is a GOT-ish section for PowerPC64. Their contents are accessed
  // through r2 register, which is reserved for that purpose. Since r2 is used
  // for accessing .got as well, .got and .toc need to be close enough in the
  // virtual address space. Usually, .toc comes just after .got. Since we place
  // .got into RELRO, .toc needs to be placed into RELRO too.
  if (Sec->Name.equals(".toc"))
    return true;

  // .got.plt contains pointers to external function symbols. They are
  // by default resolved lazily, so we usually cannot put it into RELRO.
  // However, if "-z now" is given, the lazy symbol resolution is
  // disabled, which enables us to put it into RELRO.
  if (Sec == In.GotPlt->getParent())
    return Config->ZNow;

  // .dynamic section contains data for the dynamic linker, and
  // there's no need to write to it at runtime, so it's better to put
  // it into RELRO.
  if (Sec->Name == ".dynamic")
    return true;

  // Sections with some special names are put into RELRO. This is a
  // bit unfortunate because section names shouldn't be significant in
  // ELF in spirit. But in reality many linker features depend on
  // magic section names.
  StringRef S = Sec->Name;
  return S == ".data.rel.ro" || S == ".bss.rel.ro" || S == ".ctors" ||
         S == ".dtors" || S == ".jcr" || S == ".eh_frame" ||
         S == ".openbsd.randomdata";
}

// We compute a rank for each section. The rank indicates where the
// section should be placed in the file.  Instead of using simple
// numbers (0,1,2...), we use a series of flags. One for each decision
// point when placing the section.
// Using flags has two key properties:
// * It is easy to check if a give branch was taken.
// * It is easy two see how similar two ranks are (see getRankProximity).
enum RankFlags {
  RF_NOT_ADDR_SET = 1 << 27,
  RF_NOT_ALLOC = 1 << 26,
  RF_PARTITION = 1 << 18, // Partition number (8 bits)
  RF_NOT_PART_EHDR = 1 << 17,
  RF_NOT_PART_PHDR = 1 << 16,
  RF_NOT_INTERP = 1 << 15,
  RF_NOT_NOTE = 1 << 14,
  RF_WRITE = 1 << 13,
  RF_EXEC_WRITE = 1 << 12,
  RF_EXEC = 1 << 11,
  RF_RODATA = 1 << 10,
  RF_NOT_RELRO = 1 << 9,
  RF_NOT_TLS = 1 << 8,
  RF_BSS = 1 << 7,
  RF_PPC_NOT_TOCBSS = 1 << 6,
  RF_PPC_TOCL = 1 << 5,
  RF_PPC_TOC = 1 << 4,
  RF_PPC_GOT = 1 << 3,
  RF_PPC_BRANCH_LT = 1 << 2,
  RF_MIPS_GPREL = 1 << 1,
  RF_MIPS_NOT_GOT = 1 << 0
};

static unsigned getSectionRank(const OutputSection *Sec) {
  unsigned Rank = Sec->Partition * RF_PARTITION;

  // We want to put section specified by -T option first, so we
  // can start assigning VA starting from them later.
  if (Config->SectionStartMap.count(Sec->Name))
    return Rank;
  Rank |= RF_NOT_ADDR_SET;

  // Allocatable sections go first to reduce the total PT_LOAD size and
  // so debug info doesn't change addresses in actual code.
  if (!(Sec->Flags & SHF_ALLOC))
    return Rank | RF_NOT_ALLOC;

  if (Sec->Type == SHT_LLVM_PART_EHDR)
    return Rank;
  Rank |= RF_NOT_PART_EHDR;

  if (Sec->Type == SHT_LLVM_PART_PHDR)
    return Rank;
  Rank |= RF_NOT_PART_PHDR;

  // Put .interp first because some loaders want to see that section
  // on the first page of the executable file when loaded into memory.
  if (Sec->Name == ".interp")
    return Rank;
  Rank |= RF_NOT_INTERP;

  // Put .note sections (which make up one PT_NOTE) at the beginning so that
  // they are likely to be included in a core file even if core file size is
  // limited. In particular, we want a .note.gnu.build-id and a .note.tag to be
  // included in a core to match core files with executables.
  if (Sec->Type == SHT_NOTE)
    return Rank;
  Rank |= RF_NOT_NOTE;

  // Sort sections based on their access permission in the following
  // order: R, RX, RWX, RW.  This order is based on the following
  // considerations:
  // * Read-only sections come first such that they go in the
  //   PT_LOAD covering the program headers at the start of the file.
  // * Read-only, executable sections come next.
  // * Writable, executable sections follow such that .plt on
  //   architectures where it needs to be writable will be placed
  //   between .text and .data.
  // * Writable sections come last, such that .bss lands at the very
  //   end of the last PT_LOAD.
  bool IsExec = Sec->Flags & SHF_EXECINSTR;
  bool IsWrite = Sec->Flags & SHF_WRITE;

  if (IsExec) {
    if (IsWrite)
      Rank |= RF_EXEC_WRITE;
    else
      Rank |= RF_EXEC;
  } else if (IsWrite) {
    Rank |= RF_WRITE;
  } else if (Sec->Type == SHT_PROGBITS) {
    // Make non-executable and non-writable PROGBITS sections (e.g .rodata
    // .eh_frame) closer to .text. They likely contain PC or GOT relative
    // relocations and there could be relocation overflow if other huge sections
    // (.dynstr .dynsym) were placed in between.
    Rank |= RF_RODATA;
  }

  // Place RelRo sections first. After considering SHT_NOBITS below, the
  // ordering is PT_LOAD(PT_GNU_RELRO(.data.rel.ro .bss.rel.ro) | .data .bss),
  // where | marks where page alignment happens. An alternative ordering is
  // PT_LOAD(.data | PT_GNU_RELRO( .data.rel.ro .bss.rel.ro) | .bss), but it may
  // waste more bytes due to 2 alignment places.
  if (!isRelroSection(Sec))
    Rank |= RF_NOT_RELRO;

  // If we got here we know that both A and B are in the same PT_LOAD.

  // The TLS initialization block needs to be a single contiguous block in a R/W
  // PT_LOAD, so stick TLS sections directly before the other RelRo R/W
  // sections. Since p_filesz can be less than p_memsz, place NOBITS sections
  // after PROGBITS.
  if (!(Sec->Flags & SHF_TLS))
    Rank |= RF_NOT_TLS;

  // Within TLS sections, or within other RelRo sections, or within non-RelRo
  // sections, place non-NOBITS sections first.
  if (Sec->Type == SHT_NOBITS)
    Rank |= RF_BSS;

  // Some architectures have additional ordering restrictions for sections
  // within the same PT_LOAD.
  if (Config->EMachine == EM_PPC64) {
    // PPC64 has a number of special SHT_PROGBITS+SHF_ALLOC+SHF_WRITE sections
    // that we would like to make sure appear is a specific order to maximize
    // their coverage by a single signed 16-bit offset from the TOC base
    // pointer. Conversely, the special .tocbss section should be first among
    // all SHT_NOBITS sections. This will put it next to the loaded special
    // PPC64 sections (and, thus, within reach of the TOC base pointer).
    StringRef Name = Sec->Name;
    if (Name != ".tocbss")
      Rank |= RF_PPC_NOT_TOCBSS;

    if (Name == ".toc1")
      Rank |= RF_PPC_TOCL;

    if (Name == ".toc")
      Rank |= RF_PPC_TOC;

    if (Name == ".got")
      Rank |= RF_PPC_GOT;

    if (Name == ".branch_lt")
      Rank |= RF_PPC_BRANCH_LT;
  }

  if (Config->EMachine == EM_MIPS) {
    // All sections with SHF_MIPS_GPREL flag should be grouped together
    // because data in these sections is addressable with a gp relative address.
    if (Sec->Flags & SHF_MIPS_GPREL)
      Rank |= RF_MIPS_GPREL;

    if (Sec->Name != ".got")
      Rank |= RF_MIPS_NOT_GOT;
  }

  return Rank;
}

static bool compareSections(const BaseCommand *ACmd, const BaseCommand *BCmd) {
  const OutputSection *A = cast<OutputSection>(ACmd);
  const OutputSection *B = cast<OutputSection>(BCmd);

  if (A->SortRank != B->SortRank)
    return A->SortRank < B->SortRank;

  if (!(A->SortRank & RF_NOT_ADDR_SET))
    return Config->SectionStartMap.lookup(A->Name) <
           Config->SectionStartMap.lookup(B->Name);
  return false;
}

void PhdrEntry::add(OutputSection *Sec) {
  LastSec = Sec;
  if (!FirstSec)
    FirstSec = Sec;
  p_align = std::max(p_align, Sec->Alignment);
  if (p_type == PT_LOAD)
    Sec->PtLoad = this;
}

// The beginning and the ending of .rel[a].plt section are marked
// with __rel[a]_iplt_{start,end} symbols if it is a statically linked
// executable. The runtime needs these symbols in order to resolve
// all IRELATIVE relocs on startup. For dynamic executables, we don't
// need these symbols, since IRELATIVE relocs are resolved through GOT
// and PLT. For details, see http://www.airs.com/blog/archives/403.
template <class ELFT> void Writer<ELFT>::addRelIpltSymbols() {
  if (Config->Relocatable || needsInterpSection())
    return;

  // By default, __rela_iplt_{start,end} belong to a dummy section 0
  // because .rela.plt might be empty and thus removed from output.
  // We'll override Out::ElfHeader with In.RelaIplt later when we are
  // sure that .rela.plt exists in output.
  ElfSym::RelaIpltStart = addOptionalRegular(
      Config->IsRela ? "__rela_iplt_start" : "__rel_iplt_start",
      Out::ElfHeader, 0, STV_HIDDEN, STB_WEAK);

  ElfSym::RelaIpltEnd = addOptionalRegular(
      Config->IsRela ? "__rela_iplt_end" : "__rel_iplt_end",
      Out::ElfHeader, 0, STV_HIDDEN, STB_WEAK);
}

template <class ELFT>
void Writer<ELFT>::forEachRelSec(
    llvm::function_ref<void(InputSectionBase &)> Fn) {
  // Scan all relocations. Each relocation goes through a series
  // of tests to determine if it needs special treatment, such as
  // creating GOT, PLT, copy relocations, etc.
  // Note that relocations for non-alloc sections are directly
  // processed by InputSection::relocateNonAlloc.
  for (InputSectionBase *IS : InputSections)
    if (IS->isLive() && isa<InputSection>(IS) && (IS->Flags & SHF_ALLOC))
      Fn(*IS);
  for (Partition &Part : Partitions) {
    for (EhInputSection *ES : Part.EhFrame->Sections)
      Fn(*ES);
    if (Part.ARMExidx && Part.ARMExidx->isLive())
      for (InputSection *Ex : Part.ARMExidx->ExidxSections)
        Fn(*Ex);
  }
}

// This function generates assignments for predefined symbols (e.g. _end or
// _etext) and inserts them into the commands sequence to be processed at the
// appropriate time. This ensures that the value is going to be correct by the
// time any references to these symbols are processed and is equivalent to
// defining these symbols explicitly in the linker script.
template <class ELFT> void Writer<ELFT>::setReservedSymbolSections() {
  if (ElfSym::GlobalOffsetTable) {
    // The _GLOBAL_OFFSET_TABLE_ symbol is defined by target convention usually
    // to the start of the .got or .got.plt section.
    InputSection *GotSection = In.GotPlt;
    if (!Target->GotBaseSymInGotPlt)
      GotSection = In.MipsGot ? cast<InputSection>(In.MipsGot)
                              : cast<InputSection>(In.Got);
    ElfSym::GlobalOffsetTable->Section = GotSection;
  }

  // .rela_iplt_{start,end} mark the start and the end of .rela.plt section.
  if (ElfSym::RelaIpltStart && In.RelaIplt->isNeeded()) {
    ElfSym::RelaIpltStart->Section = In.RelaIplt;
    ElfSym::RelaIpltEnd->Section = In.RelaIplt;
    ElfSym::RelaIpltEnd->Value = In.RelaIplt->getSize();
  }

  PhdrEntry *Last = nullptr;
  PhdrEntry *LastRO = nullptr;

  for (Partition &Part : Partitions) {
    for (PhdrEntry *P : Part.Phdrs) {
      if (P->p_type != PT_LOAD)
        continue;
      Last = P;
      if (!(P->p_flags & PF_W))
        LastRO = P;
    }
  }

  if (LastRO) {
    // _etext is the first location after the last read-only loadable segment.
    if (ElfSym::Etext1)
      ElfSym::Etext1->Section = LastRO->LastSec;
    if (ElfSym::Etext2)
      ElfSym::Etext2->Section = LastRO->LastSec;
  }

  if (Last) {
    // _edata points to the end of the last mapped initialized section.
    OutputSection *Edata = nullptr;
    for (OutputSection *OS : OutputSections) {
      if (OS->Type != SHT_NOBITS)
        Edata = OS;
      if (OS == Last->LastSec)
        break;
    }

    if (ElfSym::Edata1)
      ElfSym::Edata1->Section = Edata;
    if (ElfSym::Edata2)
      ElfSym::Edata2->Section = Edata;

    // _end is the first location after the uninitialized data region.
    if (ElfSym::End1)
      ElfSym::End1->Section = Last->LastSec;
    if (ElfSym::End2)
      ElfSym::End2->Section = Last->LastSec;
  }

  if (ElfSym::Bss)
    ElfSym::Bss->Section = findSection(".bss");

  // Setup MIPS _gp_disp/__gnu_local_gp symbols which should
  // be equal to the _gp symbol's value.
  if (ElfSym::MipsGp) {
    // Find GP-relative section with the lowest address
    // and use this address to calculate default _gp value.
    for (OutputSection *OS : OutputSections) {
      if (OS->Flags & SHF_MIPS_GPREL) {
        ElfSym::MipsGp->Section = OS;
        ElfSym::MipsGp->Value = 0x7ff0;
        break;
      }
    }
  }
}

// We want to find how similar two ranks are.
// The more branches in getSectionRank that match, the more similar they are.
// Since each branch corresponds to a bit flag, we can just use
// countLeadingZeros.
static int getRankProximityAux(OutputSection *A, OutputSection *B) {
  return countLeadingZeros(A->SortRank ^ B->SortRank);
}

static int getRankProximity(OutputSection *A, BaseCommand *B) {
  auto *Sec = dyn_cast<OutputSection>(B);
  return (Sec && Sec->HasInputSections) ? getRankProximityAux(A, Sec) : -1;
}

// When placing orphan sections, we want to place them after symbol assignments
// so that an orphan after
//   begin_foo = .;
//   foo : { *(foo) }
//   end_foo = .;
// doesn't break the intended meaning of the begin/end symbols.
// We don't want to go over sections since findOrphanPos is the
// one in charge of deciding the order of the sections.
// We don't want to go over changes to '.', since doing so in
//  rx_sec : { *(rx_sec) }
//  . = ALIGN(0x1000);
//  /* The RW PT_LOAD starts here*/
//  rw_sec : { *(rw_sec) }
// would mean that the RW PT_LOAD would become unaligned.
static bool shouldSkip(BaseCommand *Cmd) {
  if (auto *Assign = dyn_cast<SymbolAssignment>(Cmd))
    return Assign->Name != ".";
  return false;
}

// We want to place orphan sections so that they share as much
// characteristics with their neighbors as possible. For example, if
// both are rw, or both are tls.
static std::vector<BaseCommand *>::iterator
findOrphanPos(std::vector<BaseCommand *>::iterator B,
              std::vector<BaseCommand *>::iterator E) {
  OutputSection *Sec = cast<OutputSection>(*E);

  // Find the first element that has as close a rank as possible.
  auto I = std::max_element(B, E, [=](BaseCommand *A, BaseCommand *B) {
    return getRankProximity(Sec, A) < getRankProximity(Sec, B);
  });
  if (I == E)
    return E;

  // Consider all existing sections with the same proximity.
  int Proximity = getRankProximity(Sec, *I);
  for (; I != E; ++I) {
    auto *CurSec = dyn_cast<OutputSection>(*I);
    if (!CurSec || !CurSec->HasInputSections)
      continue;
    if (getRankProximity(Sec, CurSec) != Proximity ||
        Sec->SortRank < CurSec->SortRank)
      break;
  }

  auto IsOutputSecWithInputSections = [](BaseCommand *Cmd) {
    auto *OS = dyn_cast<OutputSection>(Cmd);
    return OS && OS->HasInputSections;
  };
  auto J = std::find_if(llvm::make_reverse_iterator(I),
                        llvm::make_reverse_iterator(B),
                        IsOutputSecWithInputSections);
  I = J.base();

  // As a special case, if the orphan section is the last section, put
  // it at the very end, past any other commands.
  // This matches bfd's behavior and is convenient when the linker script fully
  // specifies the start of the file, but doesn't care about the end (the non
  // alloc sections for example).
  auto NextSec = std::find_if(I, E, IsOutputSecWithInputSections);
  if (NextSec == E)
    return E;

  while (I != E && shouldSkip(*I))
    ++I;
  return I;
}

// Builds section order for handling --symbol-ordering-file.
static DenseMap<const InputSectionBase *, int> buildSectionOrder() {
  DenseMap<const InputSectionBase *, int> SectionOrder;
  // Use the rarely used option -call-graph-ordering-file to sort sections.
  if (!Config->CallGraphProfile.empty())
    return computeCallGraphProfileOrder();

  if (Config->SymbolOrderingFile.empty())
    return SectionOrder;

  struct SymbolOrderEntry {
    int Priority;
    bool Present;
  };

  // Build a map from symbols to their priorities. Symbols that didn't
  // appear in the symbol ordering file have the lowest priority 0.
  // All explicitly mentioned symbols have negative (higher) priorities.
  DenseMap<StringRef, SymbolOrderEntry> SymbolOrder;
  int Priority = -Config->SymbolOrderingFile.size();
  for (StringRef S : Config->SymbolOrderingFile)
    SymbolOrder.insert({S, {Priority++, false}});

  // Build a map from sections to their priorities.
  auto AddSym = [&](Symbol &Sym) {
    auto It = SymbolOrder.find(Sym.getName());
    if (It == SymbolOrder.end())
      return;
    SymbolOrderEntry &Ent = It->second;
    Ent.Present = true;

    maybeWarnUnorderableSymbol(&Sym);

    if (auto *D = dyn_cast<Defined>(&Sym)) {
      if (auto *Sec = dyn_cast_or_null<InputSectionBase>(D->Section)) {
        int &Priority = SectionOrder[cast<InputSectionBase>(Sec->Repl)];
        Priority = std::min(Priority, Ent.Priority);
      }
    }
  };

  // We want both global and local symbols. We get the global ones from the
  // symbol table and iterate the object files for the local ones.
  Symtab->forEachSymbol([&](Symbol *Sym) {
    if (!Sym->isLazy())
      AddSym(*Sym);
  });

  for (InputFile *File : ObjectFiles)
    for (Symbol *Sym : File->getSymbols())
      if (Sym->isLocal())
        AddSym(*Sym);

  if (Config->WarnSymbolOrdering)
    for (auto OrderEntry : SymbolOrder)
      if (!OrderEntry.second.Present)
        warn("symbol ordering file: no such symbol: " + OrderEntry.first);

  return SectionOrder;
}

// Sorts the sections in ISD according to the provided section order.
static void
sortISDBySectionOrder(InputSectionDescription *ISD,
                      const DenseMap<const InputSectionBase *, int> &Order) {
  std::vector<InputSection *> UnorderedSections;
  std::vector<std::pair<InputSection *, int>> OrderedSections;
  uint64_t UnorderedSize = 0;

  for (InputSection *IS : ISD->Sections) {
    auto I = Order.find(IS);
    if (I == Order.end()) {
      UnorderedSections.push_back(IS);
      UnorderedSize += IS->getSize();
      continue;
    }
    OrderedSections.push_back({IS, I->second});
  }
  llvm::sort(OrderedSections, [&](std::pair<InputSection *, int> A,
                                  std::pair<InputSection *, int> B) {
    return A.second < B.second;
  });

  // Find an insertion point for the ordered section list in the unordered
  // section list. On targets with limited-range branches, this is the mid-point
  // of the unordered section list. This decreases the likelihood that a range
  // extension thunk will be needed to enter or exit the ordered region. If the
  // ordered section list is a list of hot functions, we can generally expect
  // the ordered functions to be called more often than the unordered functions,
  // making it more likely that any particular call will be within range, and
  // therefore reducing the number of thunks required.
  //
  // For example, imagine that you have 8MB of hot code and 32MB of cold code.
  // If the layout is:
  //
  // 8MB hot
  // 32MB cold
  //
  // only the first 8-16MB of the cold code (depending on which hot function it
  // is actually calling) can call the hot code without a range extension thunk.
  // However, if we use this layout:
  //
  // 16MB cold
  // 8MB hot
  // 16MB cold
  //
  // both the last 8-16MB of the first block of cold code and the first 8-16MB
  // of the second block of cold code can call the hot code without a thunk. So
  // we effectively double the amount of code that could potentially call into
  // the hot code without a thunk.
  size_t InsPt = 0;
  if (Target->getThunkSectionSpacing() && !OrderedSections.empty()) {
    uint64_t UnorderedPos = 0;
    for (; InsPt != UnorderedSections.size(); ++InsPt) {
      UnorderedPos += UnorderedSections[InsPt]->getSize();
      if (UnorderedPos > UnorderedSize / 2)
        break;
    }
  }

  ISD->Sections.clear();
  for (InputSection *IS : makeArrayRef(UnorderedSections).slice(0, InsPt))
    ISD->Sections.push_back(IS);
  for (std::pair<InputSection *, int> P : OrderedSections)
    ISD->Sections.push_back(P.first);
  for (InputSection *IS : makeArrayRef(UnorderedSections).slice(InsPt))
    ISD->Sections.push_back(IS);
}

static void sortSection(OutputSection *Sec,
                        const DenseMap<const InputSectionBase *, int> &Order) {
  StringRef Name = Sec->Name;

  // Sort input sections by section name suffixes for
  // __attribute__((init_priority(N))).
  if (Name == ".init_array" || Name == ".fini_array") {
    if (!Script->HasSectionsCommand)
      Sec->sortInitFini();
    return;
  }

  // Sort input sections by the special rule for .ctors and .dtors.
  if (Name == ".ctors" || Name == ".dtors") {
    if (!Script->HasSectionsCommand)
      Sec->sortCtorsDtors();
    return;
  }

  // Never sort these.
  if (Name == ".init" || Name == ".fini")
    return;

  // .toc is allocated just after .got and is accessed using GOT-relative
  // relocations. Object files compiled with small code model have an
  // addressable range of [.got, .got + 0xFFFC] for GOT-relative relocations.
  // To reduce the risk of relocation overflow, .toc contents are sorted so that
  // sections having smaller relocation offsets are at beginning of .toc
  if (Config->EMachine == EM_PPC64 && Name == ".toc") {
    if (Script->HasSectionsCommand)
      return;
    assert(Sec->SectionCommands.size() == 1);
    auto *ISD = cast<InputSectionDescription>(Sec->SectionCommands[0]);
    llvm::stable_sort(ISD->Sections,
                      [](const InputSection *A, const InputSection *B) -> bool {
                        return A->File->PPC64SmallCodeModelTocRelocs &&
                               !B->File->PPC64SmallCodeModelTocRelocs;
                      });
    return;
  }

  // Sort input sections by priority using the list provided
  // by --symbol-ordering-file.
  if (!Order.empty())
    for (BaseCommand *B : Sec->SectionCommands)
      if (auto *ISD = dyn_cast<InputSectionDescription>(B))
        sortISDBySectionOrder(ISD, Order);
}

// If no layout was provided by linker script, we want to apply default
// sorting for special input sections. This also handles --symbol-ordering-file.
template <class ELFT> void Writer<ELFT>::sortInputSections() {
  // Build the order once since it is expensive.
  DenseMap<const InputSectionBase *, int> Order = buildSectionOrder();
  for (BaseCommand *Base : Script->SectionCommands)
    if (auto *Sec = dyn_cast<OutputSection>(Base))
      sortSection(Sec, Order);
}

template <class ELFT> void Writer<ELFT>::sortSections() {
  Script->adjustSectionsBeforeSorting();

  // Don't sort if using -r. It is not necessary and we want to preserve the
  // relative order for SHF_LINK_ORDER sections.
  if (Config->Relocatable)
    return;

  sortInputSections();

  for (BaseCommand *Base : Script->SectionCommands) {
    auto *OS = dyn_cast<OutputSection>(Base);
    if (!OS)
      continue;
    OS->SortRank = getSectionRank(OS);

    // We want to assign rude approximation values to OutSecOff fields
    // to know the relative order of the input sections. We use it for
    // sorting SHF_LINK_ORDER sections. See resolveShfLinkOrder().
    uint64_t I = 0;
    for (InputSection *Sec : getInputSections(OS))
      Sec->OutSecOff = I++;
  }

  if (!Script->HasSectionsCommand) {
    // We know that all the OutputSections are contiguous in this case.
    auto IsSection = [](BaseCommand *Base) { return isa<OutputSection>(Base); };
    std::stable_sort(
        llvm::find_if(Script->SectionCommands, IsSection),
        llvm::find_if(llvm::reverse(Script->SectionCommands), IsSection).base(),
        compareSections);
    return;
  }

  // Orphan sections are sections present in the input files which are
  // not explicitly placed into the output file by the linker script.
  //
  // The sections in the linker script are already in the correct
  // order. We have to figuere out where to insert the orphan
  // sections.
  //
  // The order of the sections in the script is arbitrary and may not agree with
  // compareSections. This means that we cannot easily define a strict weak
  // ordering. To see why, consider a comparison of a section in the script and
  // one not in the script. We have a two simple options:
  // * Make them equivalent (a is not less than b, and b is not less than a).
  //   The problem is then that equivalence has to be transitive and we can
  //   have sections a, b and c with only b in a script and a less than c
  //   which breaks this property.
  // * Use compareSectionsNonScript. Given that the script order doesn't have
  //   to match, we can end up with sections a, b, c, d where b and c are in the
  //   script and c is compareSectionsNonScript less than b. In which case d
  //   can be equivalent to c, a to b and d < a. As a concrete example:
  //   .a (rx) # not in script
  //   .b (rx) # in script
  //   .c (ro) # in script
  //   .d (ro) # not in script
  //
  // The way we define an order then is:
  // *  Sort only the orphan sections. They are in the end right now.
  // *  Move each orphan section to its preferred position. We try
  //    to put each section in the last position where it can share
  //    a PT_LOAD.
  //
  // There is some ambiguity as to where exactly a new entry should be
  // inserted, because Commands contains not only output section
  // commands but also other types of commands such as symbol assignment
  // expressions. There's no correct answer here due to the lack of the
  // formal specification of the linker script. We use heuristics to
  // determine whether a new output command should be added before or
  // after another commands. For the details, look at shouldSkip
  // function.

  auto I = Script->SectionCommands.begin();
  auto E = Script->SectionCommands.end();
  auto NonScriptI = std::find_if(I, E, [](BaseCommand *Base) {
    if (auto *Sec = dyn_cast<OutputSection>(Base))
      return Sec->SectionIndex == UINT32_MAX;
    return false;
  });

  // Sort the orphan sections.
  std::stable_sort(NonScriptI, E, compareSections);

  // As a horrible special case, skip the first . assignment if it is before any
  // section. We do this because it is common to set a load address by starting
  // the script with ". = 0xabcd" and the expectation is that every section is
  // after that.
  auto FirstSectionOrDotAssignment =
      std::find_if(I, E, [](BaseCommand *Cmd) { return !shouldSkip(Cmd); });
  if (FirstSectionOrDotAssignment != E &&
      isa<SymbolAssignment>(**FirstSectionOrDotAssignment))
    ++FirstSectionOrDotAssignment;
  I = FirstSectionOrDotAssignment;

  while (NonScriptI != E) {
    auto Pos = findOrphanPos(I, NonScriptI);
    OutputSection *Orphan = cast<OutputSection>(*NonScriptI);

    // As an optimization, find all sections with the same sort rank
    // and insert them with one rotate.
    unsigned Rank = Orphan->SortRank;
    auto End = std::find_if(NonScriptI + 1, E, [=](BaseCommand *Cmd) {
      return cast<OutputSection>(Cmd)->SortRank != Rank;
    });
    std::rotate(Pos, NonScriptI, End);
    NonScriptI = End;
  }

  Script->adjustSectionsAfterSorting();
}

static bool compareByFilePosition(InputSection *A, InputSection *B) {
  InputSection *LA = A->getLinkOrderDep();
  InputSection *LB = B->getLinkOrderDep();
  OutputSection *AOut = LA->getParent();
  OutputSection *BOut = LB->getParent();

  if (AOut != BOut)
    return AOut->SectionIndex < BOut->SectionIndex;
  return LA->OutSecOff < LB->OutSecOff;
}

template <class ELFT> void Writer<ELFT>::resolveShfLinkOrder() {
  for (OutputSection *Sec : OutputSections) {
    if (!(Sec->Flags & SHF_LINK_ORDER))
      continue;

    // Link order may be distributed across several InputSectionDescriptions
    // but sort must consider them all at once.
    std::vector<InputSection **> ScriptSections;
    std::vector<InputSection *> Sections;
    for (BaseCommand *Base : Sec->SectionCommands) {
      if (auto *ISD = dyn_cast<InputSectionDescription>(Base)) {
        for (InputSection *&IS : ISD->Sections) {
          ScriptSections.push_back(&IS);
          Sections.push_back(IS);
        }
      }
    }

    // The ARM.exidx section use SHF_LINK_ORDER, but we have consolidated
    // this processing inside the ARMExidxsyntheticsection::finalizeContents().
    if (!Config->Relocatable && Config->EMachine == EM_ARM &&
        Sec->Type == SHT_ARM_EXIDX)
      continue;

    llvm::stable_sort(Sections, compareByFilePosition);

    for (int I = 0, N = Sections.size(); I < N; ++I)
      *ScriptSections[I] = Sections[I];
  }
}

// We need to generate and finalize the content that depends on the address of
// InputSections. As the generation of the content may also alter InputSection
// addresses we must converge to a fixed point. We do that here. See the comment
// in Writer<ELFT>::finalizeSections().
template <class ELFT> void Writer<ELFT>::finalizeAddressDependentContent() {
  ThunkCreator TC;
  AArch64Err843419Patcher A64P;

  // For some targets, like x86, this loop iterates only once.
  for (;;) {
    bool Changed = false;

    Script->assignAddresses();

    if (Target->NeedsThunks)
      Changed |= TC.createThunks(OutputSections);

    if (Config->FixCortexA53Errata843419) {
      if (Changed)
        Script->assignAddresses();
      Changed |= A64P.createFixes();
    }

    if (In.MipsGot)
      In.MipsGot->updateAllocSize();

    for (Partition &Part : Partitions) {
      Changed |= Part.RelaDyn->updateAllocSize();
      if (Part.RelrDyn)
        Changed |= Part.RelrDyn->updateAllocSize();
    }

    if (!Changed)
      return;
  }
}

static void finalizeSynthetic(SyntheticSection *Sec) {
  if (Sec && Sec->isNeeded() && Sec->getParent())
    Sec->finalizeContents();
}

// In order to allow users to manipulate linker-synthesized sections,
// we had to add synthetic sections to the input section list early,
// even before we make decisions whether they are needed. This allows
// users to write scripts like this: ".mygot : { .got }".
//
// Doing it has an unintended side effects. If it turns out that we
// don't need a .got (for example) at all because there's no
// relocation that needs a .got, we don't want to emit .got.
//
// To deal with the above problem, this function is called after
// scanRelocations is called to remove synthetic sections that turn
// out to be empty.
static void removeUnusedSyntheticSections() {
  // All input synthetic sections that can be empty are placed after
  // all regular ones. We iterate over them all and exit at first
  // non-synthetic.
  for (InputSectionBase *S : llvm::reverse(InputSections)) {
    SyntheticSection *SS = dyn_cast<SyntheticSection>(S);
    if (!SS)
      return;
    OutputSection *OS = SS->getParent();
    if (!OS || SS->isNeeded())
      continue;

    // If we reach here, then SS is an unused synthetic section and we want to
    // remove it from corresponding input section description of output section.
    for (BaseCommand *B : OS->SectionCommands)
      if (auto *ISD = dyn_cast<InputSectionDescription>(B))
        llvm::erase_if(ISD->Sections,
                       [=](InputSection *IS) { return IS == SS; });
  }
}

// Returns true if a symbol can be replaced at load-time by a symbol
// with the same name defined in other ELF executable or DSO.
static bool computeIsPreemptible(const Symbol &B) {
  assert(!B.isLocal());

  // Only symbols that appear in dynsym can be preempted.
  if (!B.includeInDynsym())
    return false;

  // Only default visibility symbols can be preempted.
  if (B.Visibility != STV_DEFAULT)
    return false;

  // At this point copy relocations have not been created yet, so any
  // symbol that is not defined locally is preemptible.
  if (!B.isDefined())
    return true;

  // If we have a dynamic list it specifies which local symbols are preemptible.
  if (Config->HasDynamicList)
    return false;

  if (!Config->Shared)
    return false;

  // -Bsymbolic means that definitions are not preempted.
  if (Config->Bsymbolic || (Config->BsymbolicFunctions && B.isFunc()))
    return false;
  return true;
}

// Create output section objects and add them to OutputSections.
template <class ELFT> void Writer<ELFT>::finalizeSections() {
  Out::PreinitArray = findSection(".preinit_array");
  Out::InitArray = findSection(".init_array");
  Out::FiniArray = findSection(".fini_array");

  // The linker needs to define SECNAME_start, SECNAME_end and SECNAME_stop
  // symbols for sections, so that the runtime can get the start and end
  // addresses of each section by section name. Add such symbols.
  if (!Config->Relocatable) {
    addStartEndSymbols();
    for (BaseCommand *Base : Script->SectionCommands)
      if (auto *Sec = dyn_cast<OutputSection>(Base))
        addStartStopSymbols(Sec);
  }

  // Add _DYNAMIC symbol. Unlike GNU gold, our _DYNAMIC symbol has no type.
  // It should be okay as no one seems to care about the type.
  // Even the author of gold doesn't remember why gold behaves that way.
  // https://sourceware.org/ml/binutils/2002-03/msg00360.html
  if (Main->Dynamic->Parent)
    Symtab->addSymbol(Defined{/*File=*/nullptr, "_DYNAMIC", STB_WEAK,
                              STV_HIDDEN, STT_NOTYPE,
                              /*Value=*/0, /*Size=*/0, Main->Dynamic});

  // Define __rel[a]_iplt_{start,end} symbols if needed.
  addRelIpltSymbols();

  // RISC-V's gp can address +/- 2 KiB, set it to .sdata + 0x800 if not defined.
  if (Config->EMachine == EM_RISCV)
    if (!dyn_cast_or_null<Defined>(Symtab->find("__global_pointer$")))
      addOptionalRegular("__global_pointer$", findSection(".sdata"), 0x800);

  if (Config->EMachine == EM_X86_64) {
    // On targets that support TLSDESC, _TLS_MODULE_BASE_ is defined in such a
    // way that:
    //
    // 1) Without relaxation: it produces a dynamic TLSDESC relocation that
    // computes 0.
    // 2) With LD->LE relaxation: _TLS_MODULE_BASE_@tpoff = 0 (lowest address in
    // the TLS block).
    //
    // 2) is special cased in @tpoff computation. To satisfy 1), we define it as
    // an absolute symbol of zero. This is different from GNU linkers which
    // define _TLS_MODULE_BASE_ relative to the first TLS section.
    Symbol *S = Symtab->find("_TLS_MODULE_BASE_");
    if (S && S->isUndefined()) {
      S->resolve(Defined{/*File=*/nullptr, S->getName(), STB_GLOBAL, STV_HIDDEN,
                         STT_TLS, /*Value=*/0, 0,
                         /*Section=*/nullptr});
      ElfSym::TlsModuleBase = cast<Defined>(S);
    }
  }

  // This responsible for splitting up .eh_frame section into
  // pieces. The relocation scan uses those pieces, so this has to be
  // earlier.
  for (Partition &Part : Partitions)
    finalizeSynthetic(Part.EhFrame);

  Symtab->forEachSymbol([](Symbol *S) {
    if (!S->IsPreemptible)
      S->IsPreemptible = computeIsPreemptible(*S);
  });

  // Scan relocations. This must be done after every symbol is declared so that
  // we can correctly decide if a dynamic relocation is needed.
  if (!Config->Relocatable)
    forEachRelSec(scanRelocations<ELFT>);

  addIRelativeRelocs();

  if (In.Plt && In.Plt->isNeeded())
    In.Plt->addSymbols();
  if (In.Iplt && In.Iplt->isNeeded())
    In.Iplt->addSymbols();

  if (!Config->AllowShlibUndefined) {
    // Error on undefined symbols in a shared object, if all of its DT_NEEDED
    // entires are seen. These cases would otherwise lead to runtime errors
    // reported by the dynamic linker.
    //
    // ld.bfd traces all DT_NEEDED to emulate the logic of the dynamic linker to
    // catch more cases. That is too much for us. Our approach resembles the one
    // used in ld.gold, achieves a good balance to be useful but not too smart.
    for (SharedFile *File : SharedFiles)
      File->AllNeededIsKnown =
          llvm::all_of(File->DtNeeded, [&](StringRef Needed) {
            return Symtab->SoNames.count(Needed);
          });

    Symtab->forEachSymbol([](Symbol *Sym) {
      if (Sym->isUndefined() && !Sym->isWeak())
        if (auto *F = dyn_cast_or_null<SharedFile>(Sym->File))
          if (F->AllNeededIsKnown)
            error(toString(F) + ": undefined reference to " + toString(*Sym));
    });
  }

  // Now that we have defined all possible global symbols including linker-
  // synthesized ones. Visit all symbols to give the finishing touches.
  Symtab->forEachSymbol([](Symbol *Sym) {
    if (!includeInSymtab(*Sym))
      return;
    if (In.SymTab)
      In.SymTab->addSymbol(Sym);

    if (Sym->includeInDynsym()) {
      Partitions[Sym->Partition - 1].DynSymTab->addSymbol(Sym);
      if (auto *File = dyn_cast_or_null<SharedFile>(Sym->File))
        if (File->IsNeeded && !Sym->isUndefined())
          addVerneed(Sym);
    }
  });

  // We also need to scan the dynamic relocation tables of the other partitions
  // and add any referenced symbols to the partition's dynsym.
  for (Partition &Part : MutableArrayRef<Partition>(Partitions).slice(1)) {
    DenseSet<Symbol *> Syms;
    for (const SymbolTableEntry &E : Part.DynSymTab->getSymbols())
      Syms.insert(E.Sym);
    for (DynamicReloc &Reloc : Part.RelaDyn->Relocs)
      if (Reloc.Sym && !Reloc.UseSymVA && Syms.insert(Reloc.Sym).second)
        Part.DynSymTab->addSymbol(Reloc.Sym);
  }

  // Do not proceed if there was an undefined symbol.
  if (errorCount())
    return;

  if (In.MipsGot)
    In.MipsGot->build();

  removeUnusedSyntheticSections();

  sortSections();

  // Now that we have the final list, create a list of all the
  // OutputSections for convenience.
  for (BaseCommand *Base : Script->SectionCommands)
    if (auto *Sec = dyn_cast<OutputSection>(Base))
      OutputSections.push_back(Sec);

  // Prefer command line supplied address over other constraints.
  for (OutputSection *Sec : OutputSections) {
    auto I = Config->SectionStartMap.find(Sec->Name);
    if (I != Config->SectionStartMap.end())
      Sec->AddrExpr = [=] { return I->second; };
  }

  // This is a bit of a hack. A value of 0 means undef, so we set it
  // to 1 to make __ehdr_start defined. The section number is not
  // particularly relevant.
  Out::ElfHeader->SectionIndex = 1;

  for (size_t I = 0, E = OutputSections.size(); I != E; ++I) {
    OutputSection *Sec = OutputSections[I];
    Sec->SectionIndex = I + 1;
    Sec->ShName = In.ShStrTab->addString(Sec->Name);
  }

  // Binary and relocatable output does not have PHDRS.
  // The headers have to be created before finalize as that can influence the
  // image base and the dynamic section on mips includes the image base.
  if (!Config->Relocatable && !Config->OFormatBinary) {
    for (Partition &Part : Partitions) {
      Part.Phdrs = Script->hasPhdrsCommands() ? Script->createPhdrs()
                                              : createPhdrs(Part);
      if (Config->EMachine == EM_ARM) {
        // PT_ARM_EXIDX is the ARM EHABI equivalent of PT_GNU_EH_FRAME
        addPhdrForSection(Part, SHT_ARM_EXIDX, PT_ARM_EXIDX, PF_R);
      }
      if (Config->EMachine == EM_MIPS) {
        // Add separate segments for MIPS-specific sections.
        addPhdrForSection(Part, SHT_MIPS_REGINFO, PT_MIPS_REGINFO, PF_R);
        addPhdrForSection(Part, SHT_MIPS_OPTIONS, PT_MIPS_OPTIONS, PF_R);
        addPhdrForSection(Part, SHT_MIPS_ABIFLAGS, PT_MIPS_ABIFLAGS, PF_R);
      }
    }
    Out::ProgramHeaders->Size = sizeof(Elf_Phdr) * Main->Phdrs.size();

    // Find the TLS segment. This happens before the section layout loop so that
    // Android relocation packing can look up TLS symbol addresses. We only need
    // to care about the main partition here because all TLS symbols were moved
    // to the main partition (see MarkLive.cpp).
    for (PhdrEntry *P : Main->Phdrs)
      if (P->p_type == PT_TLS)
        Out::TlsPhdr = P;
  }

  // Some symbols are defined in term of program headers. Now that we
  // have the headers, we can find out which sections they point to.
  setReservedSymbolSections();

  finalizeSynthetic(In.Bss);
  finalizeSynthetic(In.BssRelRo);
  finalizeSynthetic(In.SymTabShndx);
  finalizeSynthetic(In.ShStrTab);
  finalizeSynthetic(In.StrTab);
  finalizeSynthetic(In.Got);
  finalizeSynthetic(In.MipsGot);
  finalizeSynthetic(In.IgotPlt);
  finalizeSynthetic(In.GotPlt);
  finalizeSynthetic(In.RelaIplt);
  finalizeSynthetic(In.RelaPlt);
  finalizeSynthetic(In.Plt);
  finalizeSynthetic(In.Iplt);
  finalizeSynthetic(In.PPC32Got2);
  finalizeSynthetic(In.PartIndex);

  // Dynamic section must be the last one in this list and dynamic
  // symbol table section (DynSymTab) must be the first one.
  for (Partition &Part : Partitions) {
    finalizeSynthetic(Part.ARMExidx);
    finalizeSynthetic(Part.DynSymTab);
    finalizeSynthetic(Part.GnuHashTab);
    finalizeSynthetic(Part.HashTab);
    finalizeSynthetic(Part.VerDef);
    finalizeSynthetic(Part.RelaDyn);
    finalizeSynthetic(Part.RelrDyn);
    finalizeSynthetic(Part.EhFrameHdr);
    finalizeSynthetic(Part.VerSym);
    finalizeSynthetic(Part.VerNeed);
    finalizeSynthetic(Part.Dynamic);
  }

  if (!Script->HasSectionsCommand && !Config->Relocatable)
    fixSectionAlignments();

  // SHFLinkOrder processing must be processed after relative section placements are
  // known but before addresses are allocated.
  resolveShfLinkOrder();

  // This is used to:
  // 1) Create "thunks":
  //    Jump instructions in many ISAs have small displacements, and therefore
  //    they cannot jump to arbitrary addresses in memory. For example, RISC-V
  //    JAL instruction can target only +-1 MiB from PC. It is a linker's
  //    responsibility to create and insert small pieces of code between
  //    sections to extend the ranges if jump targets are out of range. Such
  //    code pieces are called "thunks".
  //
  //    We add thunks at this stage. We couldn't do this before this point
  //    because this is the earliest point where we know sizes of sections and
  //    their layouts (that are needed to determine if jump targets are in
  //    range).
  //
  // 2) Update the sections. We need to generate content that depends on the
  //    address of InputSections. For example, MIPS GOT section content or
  //    android packed relocations sections content.
  //
  // 3) Assign the final values for the linker script symbols. Linker scripts
  //    sometimes using forward symbol declarations. We want to set the correct
  //    values. They also might change after adding the thunks.
  finalizeAddressDependentContent();

  // finalizeAddressDependentContent may have added local symbols to the static symbol table.
  finalizeSynthetic(In.SymTab);
  finalizeSynthetic(In.PPC64LongBranchTarget);

  // Fill other section headers. The dynamic table is finalized
  // at the end because some tags like RELSZ depend on result
  // of finalizing other sections.
  for (OutputSection *Sec : OutputSections)
    Sec->finalize();
}

// Ensure data sections are not mixed with executable sections when
// -execute-only is used. -execute-only is a feature to make pages executable
// but not readable, and the feature is currently supported only on AArch64.
template <class ELFT> void Writer<ELFT>::checkExecuteOnly() {
  if (!Config->ExecuteOnly)
    return;

  for (OutputSection *OS : OutputSections)
    if (OS->Flags & SHF_EXECINSTR)
      for (InputSection *IS : getInputSections(OS))
        if (!(IS->Flags & SHF_EXECINSTR))
          error("cannot place " + toString(IS) + " into " + toString(OS->Name) +
                ": -execute-only does not support intermingling data and code");
}

// The linker is expected to define SECNAME_start and SECNAME_end
// symbols for a few sections. This function defines them.
template <class ELFT> void Writer<ELFT>::addStartEndSymbols() {
  // If a section does not exist, there's ambiguity as to how we
  // define _start and _end symbols for an init/fini section. Since
  // the loader assume that the symbols are always defined, we need to
  // always define them. But what value? The loader iterates over all
  // pointers between _start and _end to run global ctors/dtors, so if
  // the section is empty, their symbol values don't actually matter
  // as long as _start and _end point to the same location.
  //
  // That said, we don't want to set the symbols to 0 (which is
  // probably the simplest value) because that could cause some
  // program to fail to link due to relocation overflow, if their
  // program text is above 2 GiB. We use the address of the .text
  // section instead to prevent that failure.
  //
  // In a rare sitaution, .text section may not exist. If that's the
  // case, use the image base address as a last resort.
  OutputSection *Default = findSection(".text");
  if (!Default)
    Default = Out::ElfHeader;

  auto Define = [=](StringRef Start, StringRef End, OutputSection *OS) {
    if (OS) {
      addOptionalRegular(Start, OS, 0);
      addOptionalRegular(End, OS, -1);
    } else {
      addOptionalRegular(Start, Default, 0);
      addOptionalRegular(End, Default, 0);
    }
  };

  Define("__preinit_array_start", "__preinit_array_end", Out::PreinitArray);
  Define("__init_array_start", "__init_array_end", Out::InitArray);
  Define("__fini_array_start", "__fini_array_end", Out::FiniArray);

  if (OutputSection *Sec = findSection(".ARM.exidx"))
    Define("__exidx_start", "__exidx_end", Sec);
}

// If a section name is valid as a C identifier (which is rare because of
// the leading '.'), linkers are expected to define __start_<secname> and
// __stop_<secname> symbols. They are at beginning and end of the section,
// respectively. This is not requested by the ELF standard, but GNU ld and
// gold provide the feature, and used by many programs.
template <class ELFT>
void Writer<ELFT>::addStartStopSymbols(OutputSection *Sec) {
  StringRef S = Sec->Name;
  if (!isValidCIdentifier(S))
    return;
  addOptionalRegular(Saver.save("__start_" + S), Sec, 0, STV_PROTECTED);
  addOptionalRegular(Saver.save("__stop_" + S), Sec, -1, STV_PROTECTED);
}

static bool needsPtLoad(OutputSection *Sec) {
  if (!(Sec->Flags & SHF_ALLOC) || Sec->Noload)
    return false;

  // Don't allocate VA space for TLS NOBITS sections. The PT_TLS PHDR is
  // responsible for allocating space for them, not the PT_LOAD that
  // contains the TLS initialization image.
  if ((Sec->Flags & SHF_TLS) && Sec->Type == SHT_NOBITS)
    return false;
  return true;
}

// Linker scripts are responsible for aligning addresses. Unfortunately, most
// linker scripts are designed for creating two PT_LOADs only, one RX and one
// RW. This means that there is no alignment in the RO to RX transition and we
// cannot create a PT_LOAD there.
static uint64_t computeFlags(uint64_t Flags) {
  if (Config->Omagic)
    return PF_R | PF_W | PF_X;
  if (Config->ExecuteOnly && (Flags & PF_X))
    return Flags & ~PF_R;
  if (Config->SingleRoRx && !(Flags & PF_W))
    return Flags | PF_X;
  return Flags;
}

// Decide which program headers to create and which sections to include in each
// one.
template <class ELFT>
std::vector<PhdrEntry *> Writer<ELFT>::createPhdrs(Partition &Part) {
  std::vector<PhdrEntry *> Ret;
  auto AddHdr = [&](unsigned Type, unsigned Flags) -> PhdrEntry * {
    Ret.push_back(make<PhdrEntry>(Type, Flags));
    return Ret.back();
  };

  unsigned PartNo = Part.getNumber();
  bool IsMain = PartNo == 1;

  // The first phdr entry is PT_PHDR which describes the program header itself.
  if (IsMain)
    AddHdr(PT_PHDR, PF_R)->add(Out::ProgramHeaders);
  else
    AddHdr(PT_PHDR, PF_R)->add(Part.ProgramHeaders->getParent());

  // PT_INTERP must be the second entry if exists.
  if (OutputSection *Cmd = findSection(".interp", PartNo))
    AddHdr(PT_INTERP, Cmd->getPhdrFlags())->add(Cmd);

  // Add the first PT_LOAD segment for regular output sections.
  uint64_t Flags = computeFlags(PF_R);
  PhdrEntry *Load = nullptr;

  // Add the headers. We will remove them if they don't fit.
  // In the other partitions the headers are ordinary sections, so they don't
  // need to be added here.
  if (IsMain) {
    Load = AddHdr(PT_LOAD, Flags);
    Load->add(Out::ElfHeader);
    Load->add(Out::ProgramHeaders);
  }

  // PT_GNU_RELRO includes all sections that should be marked as
  // read-only by dynamic linker after proccessing relocations.
  // Current dynamic loaders only support one PT_GNU_RELRO PHDR, give
  // an error message if more than one PT_GNU_RELRO PHDR is required.
  PhdrEntry *RelRo = make<PhdrEntry>(PT_GNU_RELRO, PF_R);
  bool InRelroPhdr = false;
  OutputSection *RelroEnd = nullptr;
  for (OutputSection *Sec : OutputSections) {
    if (Sec->Partition != PartNo || !needsPtLoad(Sec))
      continue;
    if (isRelroSection(Sec)) {
      InRelroPhdr = true;
      if (!RelroEnd)
        RelRo->add(Sec);
      else
        error("section: " + Sec->Name + " is not contiguous with other relro" +
              " sections");
    } else if (InRelroPhdr) {
      InRelroPhdr = false;
      RelroEnd = Sec;
    }
  }

  for (OutputSection *Sec : OutputSections) {
    if (!(Sec->Flags & SHF_ALLOC))
      break;
    if (!needsPtLoad(Sec))
      continue;

    // Normally, sections in partitions other than the current partition are
    // ignored. But partition number 255 is a special case: it contains the
    // partition end marker (.part.end). It needs to be added to the main
    // partition so that a segment is created for it in the main partition,
    // which will cause the dynamic loader to reserve space for the other
    // partitions.
    if (Sec->Partition != PartNo) {
      if (IsMain && Sec->Partition == 255)
        AddHdr(PT_LOAD, computeFlags(Sec->getPhdrFlags()))->add(Sec);
      continue;
    }

    // Segments are contiguous memory regions that has the same attributes
    // (e.g. executable or writable). There is one phdr for each segment.
    // Therefore, we need to create a new phdr when the next section has
    // different flags or is loaded at a discontiguous address or memory
    // region using AT or AT> linker script command, respectively. At the same
    // time, we don't want to create a separate load segment for the headers,
    // even if the first output section has an AT or AT> attribute.
    uint64_t NewFlags = computeFlags(Sec->getPhdrFlags());
    if (!Load ||
        ((Sec->LMAExpr ||
          (Sec->LMARegion && (Sec->LMARegion != Load->FirstSec->LMARegion))) &&
         Load->LastSec != Out::ProgramHeaders) ||
        Sec->MemRegion != Load->FirstSec->MemRegion || Flags != NewFlags ||
        Sec == RelroEnd) {
      Load = AddHdr(PT_LOAD, NewFlags);
      Flags = NewFlags;
    }

    Load->add(Sec);
  }

  // Add a TLS segment if any.
  PhdrEntry *TlsHdr = make<PhdrEntry>(PT_TLS, PF_R);
  for (OutputSection *Sec : OutputSections)
    if (Sec->Partition == PartNo && Sec->Flags & SHF_TLS)
      TlsHdr->add(Sec);
  if (TlsHdr->FirstSec)
    Ret.push_back(TlsHdr);

  // Add an entry for .dynamic.
  if (OutputSection *Sec = Part.Dynamic->getParent())
    AddHdr(PT_DYNAMIC, Sec->getPhdrFlags())->add(Sec);

  if (RelRo->FirstSec)
    Ret.push_back(RelRo);

  // PT_GNU_EH_FRAME is a special section pointing on .eh_frame_hdr.
  if (Part.EhFrame->isNeeded() && Part.EhFrameHdr &&
      Part.EhFrame->getParent() && Part.EhFrameHdr->getParent())
    AddHdr(PT_GNU_EH_FRAME, Part.EhFrameHdr->getParent()->getPhdrFlags())
        ->add(Part.EhFrameHdr->getParent());

  // PT_OPENBSD_RANDOMIZE is an OpenBSD-specific feature. That makes
  // the dynamic linker fill the segment with random data.
  if (OutputSection *Cmd = findSection(".openbsd.randomdata", PartNo))
    AddHdr(PT_OPENBSD_RANDOMIZE, Cmd->getPhdrFlags())->add(Cmd);

  // PT_GNU_STACK is a special section to tell the loader to make the
  // pages for the stack non-executable. If you really want an executable
  // stack, you can pass -z execstack, but that's not recommended for
  // security reasons.
  unsigned Perm = PF_R | PF_W;
  if (Config->ZExecstack)
    Perm |= PF_X;
  AddHdr(PT_GNU_STACK, Perm)->p_memsz = Config->ZStackSize;

  // PT_OPENBSD_WXNEEDED is a OpenBSD-specific header to mark the executable
  // is expected to perform W^X violations, such as calling mprotect(2) or
  // mmap(2) with PROT_WRITE | PROT_EXEC, which is prohibited by default on
  // OpenBSD.
  if (Config->ZWxneeded)
    AddHdr(PT_OPENBSD_WXNEEDED, PF_X);

  // Create one PT_NOTE per a group of contiguous SHT_NOTE sections with the
  // same alignment.
  PhdrEntry *Note = nullptr;
  for (OutputSection *Sec : OutputSections) {
    if (Sec->Partition != PartNo)
      continue;
    if (Sec->Type == SHT_NOTE && (Sec->Flags & SHF_ALLOC)) {
      if (!Note || Sec->LMAExpr || Note->LastSec->Alignment != Sec->Alignment)
        Note = AddHdr(PT_NOTE, PF_R);
      Note->add(Sec);
    } else {
      Note = nullptr;
    }
  }
  return Ret;
}

template <class ELFT>
void Writer<ELFT>::addPhdrForSection(Partition &Part, unsigned ShType,
                                     unsigned PType, unsigned PFlags) {
  unsigned PartNo = Part.getNumber();
  auto I = llvm::find_if(OutputSections, [=](OutputSection *Cmd) {
    return Cmd->Partition == PartNo && Cmd->Type == ShType;
  });
  if (I == OutputSections.end())
    return;

  PhdrEntry *Entry = make<PhdrEntry>(PType, PFlags);
  Entry->add(*I);
  Part.Phdrs.push_back(Entry);
}

// The first section of each PT_LOAD, the first section in PT_GNU_RELRO and the
// first section after PT_GNU_RELRO have to be page aligned so that the dynamic
// linker can set the permissions.
template <class ELFT> void Writer<ELFT>::fixSectionAlignments() {
  auto PageAlign = [](OutputSection *Cmd) {
    if (Cmd && !Cmd->AddrExpr)
      Cmd->AddrExpr = [=] {
        return alignTo(Script->getDot(), Config->MaxPageSize);
      };
  };

  for (Partition &Part : Partitions) {
    for (const PhdrEntry *P : Part.Phdrs)
      if (P->p_type == PT_LOAD && P->FirstSec)
        PageAlign(P->FirstSec);

    for (const PhdrEntry *P : Part.Phdrs) {
      if (P->p_type != PT_GNU_RELRO)
        continue;

      if (P->FirstSec)
        PageAlign(P->FirstSec);

      // Find the first section after PT_GNU_RELRO. If it is in a PT_LOAD we
      // have to align it to a page.
      auto End = OutputSections.end();
      auto I = llvm::find(OutputSections, P->LastSec);
      if (I == End || (I + 1) == End)
        continue;

      OutputSection *Cmd = (*(I + 1));
      if (needsPtLoad(Cmd))
        PageAlign(Cmd);
    }
  }
}

// Compute an in-file position for a given section. The file offset must be the
// same with its virtual address modulo the page size, so that the loader can
// load executables without any address adjustment.
static uint64_t computeFileOffset(OutputSection *OS, uint64_t Off) {
  // File offsets are not significant for .bss sections. By convention, we keep
  // section offsets monotonically increasing rather than setting to zero.
  if (OS->Type == SHT_NOBITS)
    return Off;

  // If the section is not in a PT_LOAD, we just have to align it.
  if (!OS->PtLoad)
    return alignTo(Off, OS->Alignment);

  // The first section in a PT_LOAD has to have congruent offset and address
  // module the page size.
  OutputSection *First = OS->PtLoad->FirstSec;
  if (OS == First) {
    uint64_t Alignment = std::max<uint64_t>(OS->Alignment, Config->MaxPageSize);
    return alignTo(Off, Alignment, OS->Addr);
  }

  // If two sections share the same PT_LOAD the file offset is calculated
  // using this formula: Off2 = Off1 + (VA2 - VA1).
  return First->Offset + OS->Addr - First->Addr;
}

// Set an in-file position to a given section and returns the end position of
// the section.
static uint64_t setFileOffset(OutputSection *OS, uint64_t Off) {
  Off = computeFileOffset(OS, Off);
  OS->Offset = Off;

  if (OS->Type == SHT_NOBITS)
    return Off;
  return Off + OS->Size;
}

template <class ELFT> void Writer<ELFT>::assignFileOffsetsBinary() {
  uint64_t Off = 0;
  for (OutputSection *Sec : OutputSections)
    if (Sec->Flags & SHF_ALLOC)
      Off = setFileOffset(Sec, Off);
  FileSize = alignTo(Off, Config->Wordsize);
}

static std::string rangeToString(uint64_t Addr, uint64_t Len) {
  return "[0x" + utohexstr(Addr) + ", 0x" + utohexstr(Addr + Len - 1) + "]";
}

// Assign file offsets to output sections.
template <class ELFT> void Writer<ELFT>::assignFileOffsets() {
  uint64_t Off = 0;
  Off = setFileOffset(Out::ElfHeader, Off);
  Off = setFileOffset(Out::ProgramHeaders, Off);

  PhdrEntry *LastRX = nullptr;
  for (Partition &Part : Partitions)
    for (PhdrEntry *P : Part.Phdrs)
      if (P->p_type == PT_LOAD && (P->p_flags & PF_X))
        LastRX = P;

  for (OutputSection *Sec : OutputSections) {
    Off = setFileOffset(Sec, Off);
    if (Script->HasSectionsCommand)
      continue;

    // If this is a last section of the last executable segment and that
    // segment is the last loadable segment, align the offset of the
    // following section to avoid loading non-segments parts of the file.
    if (LastRX && LastRX->LastSec == Sec)
      Off = alignTo(Off, Config->CommonPageSize);
  }

  SectionHeaderOff = alignTo(Off, Config->Wordsize);
  FileSize = SectionHeaderOff + (OutputSections.size() + 1) * sizeof(Elf_Shdr);

  // Our logic assumes that sections have rising VA within the same segment.
  // With use of linker scripts it is possible to violate this rule and get file
  // offset overlaps or overflows. That should never happen with a valid script
  // which does not move the location counter backwards and usually scripts do
  // not do that. Unfortunately, there are apps in the wild, for example, Linux
  // kernel, which control segment distribution explicitly and move the counter
  // backwards, so we have to allow doing that to support linking them. We
  // perform non-critical checks for overlaps in checkSectionOverlap(), but here
  // we want to prevent file size overflows because it would crash the linker.
  for (OutputSection *Sec : OutputSections) {
    if (Sec->Type == SHT_NOBITS)
      continue;
    if ((Sec->Offset > FileSize) || (Sec->Offset + Sec->Size > FileSize))
      error("unable to place section " + Sec->Name + " at file offset " +
            rangeToString(Sec->Offset, Sec->Size) +
            "; check your linker script for overflows");
  }
}

// Finalize the program headers. We call this function after we assign
// file offsets and VAs to all sections.
template <class ELFT> void Writer<ELFT>::setPhdrs(Partition &Part) {
  for (PhdrEntry *P : Part.Phdrs) {
    OutputSection *First = P->FirstSec;
    OutputSection *Last = P->LastSec;

    if (First) {
      P->p_filesz = Last->Offset - First->Offset;
      if (Last->Type != SHT_NOBITS)
        P->p_filesz += Last->Size;

      P->p_memsz = Last->Addr + Last->Size - First->Addr;
      P->p_offset = First->Offset;
      P->p_vaddr = First->Addr;

      // File offsets in partitions other than the main partition are relative
      // to the offset of the ELF headers. Perform that adjustment now.
      if (Part.ElfHeader)
        P->p_offset -= Part.ElfHeader->getParent()->Offset;

      if (!P->HasLMA)
        P->p_paddr = First->getLMA();
    }

    if (P->p_type == PT_LOAD) {
      P->p_align = std::max<uint64_t>(P->p_align, Config->MaxPageSize);
    } else if (P->p_type == PT_GNU_RELRO) {
      P->p_align = 1;
      // The glibc dynamic loader rounds the size down, so we need to round up
      // to protect the last page. This is a no-op on FreeBSD which always
      // rounds up.
      P->p_memsz = alignTo(P->p_memsz, Config->CommonPageSize);
    }
  }
}

// A helper struct for checkSectionOverlap.
namespace {
struct SectionOffset {
  OutputSection *Sec;
  uint64_t Offset;
};
} // namespace

// Check whether sections overlap for a specific address range (file offsets,
// load and virtual adresses).
static void checkOverlap(StringRef Name, std::vector<SectionOffset> &Sections,
                         bool IsVirtualAddr) {
  llvm::sort(Sections, [=](const SectionOffset &A, const SectionOffset &B) {
    return A.Offset < B.Offset;
  });

  // Finding overlap is easy given a vector is sorted by start position.
  // If an element starts before the end of the previous element, they overlap.
  for (size_t I = 1, End = Sections.size(); I < End; ++I) {
    SectionOffset A = Sections[I - 1];
    SectionOffset B = Sections[I];
    if (B.Offset >= A.Offset + A.Sec->Size)
      continue;

    // If both sections are in OVERLAY we allow the overlapping of virtual
    // addresses, because it is what OVERLAY was designed for.
    if (IsVirtualAddr && A.Sec->InOverlay && B.Sec->InOverlay)
      continue;

    errorOrWarn("section " + A.Sec->Name + " " + Name +
                " range overlaps with " + B.Sec->Name + "\n>>> " + A.Sec->Name +
                " range is " + rangeToString(A.Offset, A.Sec->Size) + "\n>>> " +
                B.Sec->Name + " range is " +
                rangeToString(B.Offset, B.Sec->Size));
  }
}

// Check for overlapping sections and address overflows.
//
// In this function we check that none of the output sections have overlapping
// file offsets. For SHF_ALLOC sections we also check that the load address
// ranges and the virtual address ranges don't overlap
template <class ELFT> void Writer<ELFT>::checkSections() {
  // First, check that section's VAs fit in available address space for target.
  for (OutputSection *OS : OutputSections)
    if ((OS->Addr + OS->Size < OS->Addr) ||
        (!ELFT::Is64Bits && OS->Addr + OS->Size > UINT32_MAX))
      errorOrWarn("section " + OS->Name + " at 0x" + utohexstr(OS->Addr) +
                  " of size 0x" + utohexstr(OS->Size) +
                  " exceeds available address space");

  // Check for overlapping file offsets. In this case we need to skip any
  // section marked as SHT_NOBITS. These sections don't actually occupy space in
  // the file so Sec->Offset + Sec->Size can overlap with others. If --oformat
  // binary is specified only add SHF_ALLOC sections are added to the output
  // file so we skip any non-allocated sections in that case.
  std::vector<SectionOffset> FileOffs;
  for (OutputSection *Sec : OutputSections)
    if (Sec->Size > 0 && Sec->Type != SHT_NOBITS &&
        (!Config->OFormatBinary || (Sec->Flags & SHF_ALLOC)))
      FileOffs.push_back({Sec, Sec->Offset});
  checkOverlap("file", FileOffs, false);

  // When linking with -r there is no need to check for overlapping virtual/load
  // addresses since those addresses will only be assigned when the final
  // executable/shared object is created.
  if (Config->Relocatable)
    return;

  // Checking for overlapping virtual and load addresses only needs to take
  // into account SHF_ALLOC sections since others will not be loaded.
  // Furthermore, we also need to skip SHF_TLS sections since these will be
  // mapped to other addresses at runtime and can therefore have overlapping
  // ranges in the file.
  std::vector<SectionOffset> VMAs;
  for (OutputSection *Sec : OutputSections)
    if (Sec->Size > 0 && (Sec->Flags & SHF_ALLOC) && !(Sec->Flags & SHF_TLS))
      VMAs.push_back({Sec, Sec->Addr});
  checkOverlap("virtual address", VMAs, true);

  // Finally, check that the load addresses don't overlap. This will usually be
  // the same as the virtual addresses but can be different when using a linker
  // script with AT().
  std::vector<SectionOffset> LMAs;
  for (OutputSection *Sec : OutputSections)
    if (Sec->Size > 0 && (Sec->Flags & SHF_ALLOC) && !(Sec->Flags & SHF_TLS))
      LMAs.push_back({Sec, Sec->getLMA()});
  checkOverlap("load address", LMAs, false);
}

// The entry point address is chosen in the following ways.
//
// 1. the '-e' entry command-line option;
// 2. the ENTRY(symbol) command in a linker control script;
// 3. the value of the symbol _start, if present;
// 4. the number represented by the entry symbol, if it is a number;
// 5. the address of the first byte of the .text section, if present;
// 6. the address 0.
static uint64_t getEntryAddr() {
  // Case 1, 2 or 3
  if (Symbol *B = Symtab->find(Config->Entry))
    return B->getVA();

  // Case 4
  uint64_t Addr;
  if (to_integer(Config->Entry, Addr))
    return Addr;

  // Case 5
  if (OutputSection *Sec = findSection(".text")) {
    if (Config->WarnMissingEntry)
      warn("cannot find entry symbol " + Config->Entry + "; defaulting to 0x" +
           utohexstr(Sec->Addr));
    return Sec->Addr;
  }

  // Case 6
  if (Config->WarnMissingEntry)
    warn("cannot find entry symbol " + Config->Entry +
         "; not setting start address");
  return 0;
}

static uint16_t getELFType() {
  if (Config->Pic)
    return ET_DYN;
  if (Config->Relocatable)
    return ET_REL;
  return ET_EXEC;
}

template <class ELFT> void Writer<ELFT>::writeHeader() {
  writeEhdr<ELFT>(Out::BufferStart, *Main);
  writePhdrs<ELFT>(Out::BufferStart + sizeof(Elf_Ehdr), *Main);

  auto *EHdr = reinterpret_cast<Elf_Ehdr *>(Out::BufferStart);
  EHdr->e_type = getELFType();
  EHdr->e_entry = getEntryAddr();
  EHdr->e_shoff = SectionHeaderOff;

  // Write the section header table.
  //
  // The ELF header can only store numbers up to SHN_LORESERVE in the e_shnum
  // and e_shstrndx fields. When the value of one of these fields exceeds
  // SHN_LORESERVE ELF requires us to put sentinel values in the ELF header and
  // use fields in the section header at index 0 to store
  // the value. The sentinel values and fields are:
  // e_shnum = 0, SHdrs[0].sh_size = number of sections.
  // e_shstrndx = SHN_XINDEX, SHdrs[0].sh_link = .shstrtab section index.
  auto *SHdrs = reinterpret_cast<Elf_Shdr *>(Out::BufferStart + EHdr->e_shoff);
  size_t Num = OutputSections.size() + 1;
  if (Num >= SHN_LORESERVE)
    SHdrs->sh_size = Num;
  else
    EHdr->e_shnum = Num;

  uint32_t StrTabIndex = In.ShStrTab->getParent()->SectionIndex;
  if (StrTabIndex >= SHN_LORESERVE) {
    SHdrs->sh_link = StrTabIndex;
    EHdr->e_shstrndx = SHN_XINDEX;
  } else {
    EHdr->e_shstrndx = StrTabIndex;
  }

  for (OutputSection *Sec : OutputSections)
    Sec->writeHeaderTo<ELFT>(++SHdrs);
}

// Open a result file.
template <class ELFT> void Writer<ELFT>::openFile() {
  uint64_t MaxSize = Config->Is64 ? INT64_MAX : UINT32_MAX;
  if (FileSize != size_t(FileSize) || MaxSize < FileSize) {
    error("output file too large: " + Twine(FileSize) + " bytes");
    return;
  }

  unlinkAsync(Config->OutputFile);
  unsigned Flags = 0;
  if (!Config->Relocatable)
    Flags = FileOutputBuffer::F_executable;
  Expected<std::unique_ptr<FileOutputBuffer>> BufferOrErr =
      FileOutputBuffer::create(Config->OutputFile, FileSize, Flags);

  if (!BufferOrErr) {
    error("failed to open " + Config->OutputFile + ": " +
          llvm::toString(BufferOrErr.takeError()));
    return;
  }
  Buffer = std::move(*BufferOrErr);
  Out::BufferStart = Buffer->getBufferStart();
}

template <class ELFT> void Writer<ELFT>::writeSectionsBinary() {
  for (OutputSection *Sec : OutputSections)
    if (Sec->Flags & SHF_ALLOC)
      Sec->writeTo<ELFT>(Out::BufferStart + Sec->Offset);
}

static void fillTrap(uint8_t *I, uint8_t *End) {
  for (; I + 4 <= End; I += 4)
    memcpy(I, &Target->TrapInstr, 4);
}

// Fill the last page of executable segments with trap instructions
// instead of leaving them as zero. Even though it is not required by any
// standard, it is in general a good thing to do for security reasons.
//
// We'll leave other pages in segments as-is because the rest will be
// overwritten by output sections.
template <class ELFT> void Writer<ELFT>::writeTrapInstr() {
  if (Script->HasSectionsCommand)
    return;

  for (Partition &Part : Partitions) {
    // Fill the last page.
    for (PhdrEntry *P : Part.Phdrs)
      if (P->p_type == PT_LOAD && (P->p_flags & PF_X))
        fillTrap(Out::BufferStart + alignDown(P->FirstSec->Offset + P->p_filesz,
                                              Config->CommonPageSize),
                 Out::BufferStart + alignTo(P->FirstSec->Offset + P->p_filesz,
                                            Config->CommonPageSize));

    // Round up the file size of the last segment to the page boundary iff it is
    // an executable segment to ensure that other tools don't accidentally
    // trim the instruction padding (e.g. when stripping the file).
    PhdrEntry *Last = nullptr;
    for (PhdrEntry *P : Part.Phdrs)
      if (P->p_type == PT_LOAD)
        Last = P;

    if (Last && (Last->p_flags & PF_X))
      Last->p_memsz = Last->p_filesz =
          alignTo(Last->p_filesz, Config->CommonPageSize);
  }
}

// Write section contents to a mmap'ed file.
template <class ELFT> void Writer<ELFT>::writeSections() {
  // In -r or -emit-relocs mode, write the relocation sections first as in
  // ELf_Rel targets we might find out that we need to modify the relocated
  // section while doing it.
  for (OutputSection *Sec : OutputSections)
    if (Sec->Type == SHT_REL || Sec->Type == SHT_RELA)
      Sec->writeTo<ELFT>(Out::BufferStart + Sec->Offset);

  for (OutputSection *Sec : OutputSections)
    if (Sec->Type != SHT_REL && Sec->Type != SHT_RELA)
      Sec->writeTo<ELFT>(Out::BufferStart + Sec->Offset);
}

// Split one uint8 array into small pieces of uint8 arrays.
static std::vector<ArrayRef<uint8_t>> split(ArrayRef<uint8_t> Arr,
                                            size_t ChunkSize) {
  std::vector<ArrayRef<uint8_t>> Ret;
  while (Arr.size() > ChunkSize) {
    Ret.push_back(Arr.take_front(ChunkSize));
    Arr = Arr.drop_front(ChunkSize);
  }
  if (!Arr.empty())
    Ret.push_back(Arr);
  return Ret;
}

// Computes a hash value of Data using a given hash function.
// In order to utilize multiple cores, we first split data into 1MB
// chunks, compute a hash for each chunk, and then compute a hash value
// of the hash values.
static void
computeHash(llvm::MutableArrayRef<uint8_t> HashBuf,
            llvm::ArrayRef<uint8_t> Data,
            std::function<void(uint8_t *Dest, ArrayRef<uint8_t> Arr)> HashFn) {
  std::vector<ArrayRef<uint8_t>> Chunks = split(Data, 1024 * 1024);
  std::vector<uint8_t> Hashes(Chunks.size() * HashBuf.size());

  // Compute hash values.
  parallelForEachN(0, Chunks.size(), [&](size_t I) {
    HashFn(Hashes.data() + I * HashBuf.size(), Chunks[I]);
  });

  // Write to the final output buffer.
  HashFn(HashBuf.data(), Hashes);
}

template <class ELFT> void Writer<ELFT>::writeBuildId() {
  if (!Main->BuildId || !Main->BuildId->getParent())
    return;

  if (Config->BuildId == BuildIdKind::Hexstring) {
    for (Partition &Part : Partitions)
      Part.BuildId->writeBuildId(Config->BuildIdVector);
    return;
  }

  // Compute a hash of all sections of the output file.
  size_t HashSize = Main->BuildId->HashSize;
  std::vector<uint8_t> BuildId(HashSize);
  llvm::ArrayRef<uint8_t> Buf{Out::BufferStart, size_t(FileSize)};

  switch (Config->BuildId) {
  case BuildIdKind::Fast:
    computeHash(BuildId, Buf, [](uint8_t *Dest, ArrayRef<uint8_t> Arr) {
      write64le(Dest, xxHash64(Arr));
    });
    break;
  case BuildIdKind::Md5:
    computeHash(BuildId, Buf, [&](uint8_t *Dest, ArrayRef<uint8_t> Arr) {
      memcpy(Dest, MD5::hash(Arr).data(), HashSize);
    });
    break;
  case BuildIdKind::Sha1:
    computeHash(BuildId, Buf, [&](uint8_t *Dest, ArrayRef<uint8_t> Arr) {
      memcpy(Dest, SHA1::hash(Arr).data(), HashSize);
    });
    break;
  case BuildIdKind::Uuid:
    if (auto EC = llvm::getRandomBytes(BuildId.data(), HashSize))
      error("entropy source failure: " + EC.message());
    break;
  default:
    llvm_unreachable("unknown BuildIdKind");
  }
  for (Partition &Part : Partitions)
    Part.BuildId->writeBuildId(BuildId);
}

template void elf::writeResult<ELF32LE>();
template void elf::writeResult<ELF32BE>();
template void elf::writeResult<ELF64LE>();
template void elf::writeResult<ELF64BE>();
