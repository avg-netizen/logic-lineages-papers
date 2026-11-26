module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Success-only fuel transport through the actual kernel. All leaves except
for the explicit saturated axiom wrapper remain arbitrary; no native Boolean
range, calibration or abstract dispatcher monotonicity premise is supplied. -/
def InternalStep : Prop :=
 ∀ (valid logical arithmetic : Program 1) (x : Program 3),
 ∀ n (p : Program n) (ktag ptag ctag : Nat),
 (nodes p)[ktag]? = some ⟨3,HistoryKernel.kernel valid logical arithmetic (SaturatedAxiomLeaf.saturated x)⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (index s t h lines out rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (stepTransport ktag ptag index s t h lines out rest))

/-- Actual internally arbitrary-count successful-run fuel transport. This
requires genuine source induction and positive-output provenance: low-fuel
NONE cannot be used as a successful history. The high-fuel run retains the
identical requested result, but nothing is claimed about rejected low runs. -/
def InternalIterator : Prop :=
 ∀ (valid logical arithmetic : Program 1) (x : Program 3),
 ∀ n (p : Program n) (itag ptag ctag : Nat),
 (nodes p)[itag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator
   (HistoryKernel.kernel valid logical arithmetic (SaturatedAxiomLeaf.saturated x))⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (count index s t h lines out rest : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (iteratorTransport itag ptag count index s t h lines out rest))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedKernelFuel.Targets
