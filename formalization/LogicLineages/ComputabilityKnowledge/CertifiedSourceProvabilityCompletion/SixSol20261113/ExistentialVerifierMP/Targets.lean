module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open LiteralValidatedMPRun LiteralRawMP
/-- Exact original verifier/canonical-constructor nodes and literal validator,
with the explicitly saturated axiom leaf. No free fuel or certificate witness,
actual successful run, semantic formula validity, native calibration, Boolean
range, monotonicity or provability-MP premise is assumed. All witnesses must be
eliminated/introduced inside the unchanged arithmetic derivation calculus.
This is generic ordinary raw-code verifier provability, not published Pr_D,
its fixed diagonal rho, implication quotation normalization or HB2/HB3. -/
def InternalProvabilityMP : Prop := ∀ (l a : Program 1) (baseX : Program 3), ∀ n (p : Program n)
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
  ∀ ctx (index context phi psi : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
   (distribution vtag atag ctag index context phi psi))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.Targets
