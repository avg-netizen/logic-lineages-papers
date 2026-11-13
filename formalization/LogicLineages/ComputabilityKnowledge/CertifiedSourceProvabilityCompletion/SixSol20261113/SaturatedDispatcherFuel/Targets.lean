module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
/-- Internal fuel monotonicity of the actual dispatcher with the explicit
saturated axiom leaf. All other leaves are arbitrary Programs, not calibrated
or assumed Boolean. The same index, history and line are retained, including
malformed/default codes. The axiom child's internal monotonicity and every
other branch's fuel independence must be derived from their literal ASTs.
No branch-success, native calibration, source identity or checker monotonicity
premise is supplied. This is a dispatcher lemma, not full kernel/iterator/HB. -/
def InternalMonotonicity : Prop :=
 ∀ (valid logical arithmetic : Program 1) (x : Program 3),
 ∀ n (p : Program n) (tag : Nat),
 (nodes p)[tag]? = some ⟨4,HistoryDispatcher.lineDispatcher valid logical arithmetic
   (SaturatedAxiomLeaf.saturated x)⟩ →
 ∀ ctx (index s t history line : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (SixSol20261112.Fuel.orderGuard s t)
   (.imp (acceptance tag index s history line) (acceptance tag index t history line))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Targets
