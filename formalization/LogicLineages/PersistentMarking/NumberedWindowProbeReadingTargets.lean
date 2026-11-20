module
public import LogicLineages.PersistentMarking.NumberedWindowInternalProbeTargets
public import LogicLineages.PersistentMarking.NumberedWindowProbeCode
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowProbeReadingTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus
open NumberedWindowInternalProbeTargets (typedAt freshAt witnesses typeCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

def ExactProbeTypeCoding := ∀ τ : Ty, typeCode τ = NumberedWindowProbeCode.code τ
def ExactProbeReading : Prop :=
  ∀ (ty : Nat → Nat → Bool) (pick : Nat → Option Nat) (app : Nat → Nat → Nat → Bool)
    (h : Program 2) (a : Program 1) (p : Program 3),
    (∀ t n, evaluate h (t ::ᵥ n ::ᵥ nil) = (ty t n).toNat) →
    (∀ n, evaluate a (n ::ᵥ nil) = Encodable.encode (pick n)) →
    (∀ f u v, evaluate p (f ::ᵥ u ::ᵥ v ::ᵥ nil) = (app f u v).toNat) →
    ∀ (τ : Ty) (α : Type) (q : OrdinaryArithmetic.Term α) (P : Nat → Prop) (env : α → Nat),
      (realize P (typedAt h τ q) env ↔ ty (NumberedWindowProbeCode.code τ) (q.realize env) = true) ∧
      (realize P (witnesses p h a τ q) env ↔ ∃ u v,
        pick (q.realize env) = some u ∧ app (q.realize env) u v = true ∧
        ty (NumberedWindowProbeCode.code τ) v = true)
end LogicLineages.PersistentMarking.NumberedWindowProbeReadingTargets
