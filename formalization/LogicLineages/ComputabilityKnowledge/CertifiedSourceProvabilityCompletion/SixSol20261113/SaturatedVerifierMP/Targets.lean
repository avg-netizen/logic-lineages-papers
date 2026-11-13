module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open LiteralValidatedMPRun LiteralRawMP
/-- The actual outer bounded-search verifier, literal line validator and
explicitly saturated axiom leaf. All supplied registry nodes are exact ASTs
already needed for the original canonical MP constructor. No input successful
runs, newly constructed line validity, native calibration, Boolean range or
core/fuel monotonicity is assumed. Those internal bridges must be proved.
Different input fuels are aligned at s+t inside arithmetic, not externally.
No same-published-source/HB claim or numbered statement promotion. -/
def InternalVerifierMP : Prop := ∀ (l a : Program 1) (baseX : Program 3), ∀ n (p : Program n)
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
  ∀ ctx (context phi psi imp ant index s t : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (preservation vtag atag ctag mtag context phi psi imp ant index s t))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Targets
