module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open LiteralValidatedMPRun LiteralRawMP
/-- Fixed external sentence quotation MP, obtained from actual registry
numeral calculations and internal raw provability MP. No runtime semantic
formula-validity premise or unproved quotation equation is assumed. The same
exact actual registry nodes remain explicit. No published Pr_D/HB claim. -/
def InternalQuotedMP : Prop := ∀ (l a : Program 1) (baseX : Program 3), ∀ n (p : Program n)
  (itag ltag atag ptag ctag dtag droptag rtag dispatcherTag : Nat),
  (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (HistoryKernel.kernel validity l a (SaturatedAxiomLeaf.saturated baseX))⟩ →
  (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩ →
  (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
  (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
  (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩ →
  (nodes p)[droptag]? = some ⟨2,HistoryLookup.drop⟩ →
  (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩ →
  (nodes p)[dispatcherTag]? = some ⟨4,HistoryDispatcher.lineDispatcher validity l a (SaturatedAxiomLeaf.saturated baseX)⟩ →
  ∀ (mtag qtag vtag : Nat),
  (nodes p)[mtag]? = some ⟨4,constructor⟩ →
  (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker validity l a (SaturatedAxiomLeaf.saturated baseX)
    LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
  (nodes p)[vtag]? = some ⟨5,LiteralKernelSource.verifier validity l a (SaturatedAxiomLeaf.saturated baseX)
    LiteralCheckerAuxiliaries.bound LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
  ∀ ctx (index : Term ctx) (sigma tau : Sentence),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (distribution vtag index sigma tau))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Targets
