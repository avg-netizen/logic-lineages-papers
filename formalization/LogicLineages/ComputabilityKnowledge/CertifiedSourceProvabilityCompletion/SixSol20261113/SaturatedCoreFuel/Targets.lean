module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Actual original core checker with bound=encoded certificate, initial
pair(1,certificate), and original finalizer. Only the axiom leaf is explicitly
saturated. The sole registry premise installs that actual core: all auxiliary
subtree locations must be derived. Runtime index, requested context/formula,
certificate, and iteration count remain unchanged as the internal fuel bound
increases. No successful-run, validity, native calibration, Boolean-core,
source-identity or core-monotonicity premise is supplied. -/
def InternalMonotonicity : Prop :=
 ∀ (valid logical arithmetic : Program 1) (x : Program 3),
 ∀ n (p : Program n) (qtag : Nat),
 (nodes p)[qtag]? = some ⟨5,LiteralKernelSource.coreChecker valid logical arithmetic
   (SaturatedAxiomLeaf.saturated x) LiteralCheckerAuxiliaries.bound
   LiteralCheckerAuxiliaries.initial LiteralCheckerAuxiliaries.finalizer⟩ →
 ∀ ctx (index s t context formula certificate : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (SixSol20261112.Fuel.orderGuard s t)
   (.imp (acceptance qtag index s context formula certificate)
    (acceptance qtag index t context formula certificate))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedCoreFuel.Targets
