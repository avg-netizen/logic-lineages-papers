module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open TwoSol20261113.ReflexivityCertificate
/-- Actual saturated verifier accepts the original singleton reflexivity certificate
at every symbolic runtime vector and every index/fuel, including zero fuel.
Only literal AST lookups are premises; neither success nor monotonicity is assumed.
This is not a cumulative source installation or general HB3 theorem. -/
def InternalSaturatedCertificate : Prop :=
 ∀ k (t : Term k) (old arithmetic : Program 1) (x : Program 3)
 n (p : Program n) (I : Installation p t old arithmetic x) (vtag : Nat),
 (nodes p)[vtag]? = some ⟨5,ReflexivityFuel.checker old arithmetic x⟩ →
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (SixSol20261112.Fuel.success vtag index fuel .zero
   (.add (raw I.etag values) (raw I.etag values)) (certificate I.ctag I.qtag values)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.Targets
