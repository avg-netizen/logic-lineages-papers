import LogicLineages.PersistentMarking.ProtectedSpineLawTargets

namespace LogicLineages.PersistentMarking.ProtectedSpineAgreementTargets
open Spine DecisionPorts FiniteDomainSchema FiniteDomainFoundation HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineLaws
open ProtectedSpineInterpreterCore (Evaluation)
open ProtectedSpineEnvironment (freeCode boundCode)

abbrev FrameRelation := Context → Assignments → Assignments → Prop

structure Agreement (E : Environment) (σ : Ty) (ev ev' : Evaluation) (R : FrameRelation)
    (P : Nat → Nat → Prop) : Prop where
  value : ∀ Γ a b, InputValid E Γ a → InputValid E Γ b → R Γ a b →
    ValueEq E σ Γ (valueAt ev Γ a) (valueAt ev' Γ b)
  call : ∀ Γ a b k l ds τ xs, InputValid E Γ a → InputValid E Γ b → R Γ a b → P k l →
    (ds,τ) ∈ fullPrefixes σ → TupleValues E Γ ds xs →
    nonemptyAt E ev Γ a k ds τ xs = nonemptyAt E ev' Γ b l ds τ xs

def SameInputs (E : Environment) (C : BoundContext) : FrameRelation :=
  fun Γ a b =>
    (∀ σ x, freeCode E Γ a.free σ x = freeCode E Γ b.free σ x) ∧
    ∀ σ i, C i = some σ → boundCode E Γ a.bound σ i = boundCode E Γ b.bound σ i

def SameProtection (C : BoundContext) (k l : Nat) : Prop :=
  ∀ σ i, C i = some σ → (i < k ↔ i < l)

def ScopeAgreement : Prop := ∀ S E H M C q σ, Typed C q σ → Covered E H q →
  Agreement E σ (ProtectedSpineInterpreter.evaluate S E H M q) (ProtectedSpineInterpreter.evaluate S E H M q)
    (SameInputs E C) (SameProtection C)

end LogicLineages.PersistentMarking.ProtectedSpineAgreementTargets
