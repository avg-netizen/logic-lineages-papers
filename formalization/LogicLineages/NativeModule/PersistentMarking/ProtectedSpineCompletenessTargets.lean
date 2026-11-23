module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineAdequacyBase

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineCompletenessTargets
open Spine DecisionPorts DecisionRequests FiniteDomainSchema HereditaryDomainCode
open PortNormalization ProtectedSpineAdequacyTargets ProtectedSpineAdequacyBase ProtectedSpineFixedApplicationTargets

def concreteTags (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (qs : Args) :
    List MarkedExtras.Tagged := closedCodes S (domain F) F.data.sourceHeads M Γ qs

def ownerAt (S : Signature) (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (τ : Ty) (bs es : Args) :
    MarkedFamilyParameters.Parameter :=
  ProtectedSpineInterpreterCore.parameter (domain F) f τ Γ
    (concreteTags S F M Γ bs) (concreteTags S F M Γ es)

def WeakGoal (F : Inputs S) (M : Code) (Γ : Context) (q t : Expr) : Prop :=
  Invariant F (.weak Γ q t) → (unfoldedValue S F M Γ q).weak Γ t = true

def StrictGoal (F : Inputs S) (M : Code) (Γ : Context) (q t : Expr) : Prop :=
  Invariant F (.strict Γ q t) → (unfoldedValue S F M Γ q).strict Γ t = true

def MatchingGoal (F : Inputs S) (M : Code) (Γ : Context) (qs ts : Args) : Prop :=
  Invariant F (.matching Γ qs ts) →
  MarkedConstructorTargets.Matches (domain F) Γ (concreteTags S F M Γ qs) (MarkedConstructorTests.terms ts)

def MultisetGoal (F : Inputs S) (M : Code) (Γ : Context) (qs ts : Args) : Prop :=
  Invariant F (.multiset Γ qs ts) →
  MarkedConstructorTargets.Replaces (domain F) Γ (concreteTags S F M Γ qs) (MarkedConstructorTests.terms ts)

def CoverageGoal (F : Inputs S) (M : Code) (Γ : Context) (qs ts : Args) : Prop :=
  Invariant F (.coverage Γ qs ts) → ∀ t, t ∈ MarkedConstructorTests.terms ts →
    ∃ a, a ∈ concreteTags S F M Γ qs ∧ MarkedConstructorTests.bit true (domain F) Γ a t = true

def WholeGoal (F : Inputs S) (M : Code) (Γ : Context) (f : Head) (bs es ts : Args) : Prop :=
  Invariant F (.whole Γ f bs es ts) → ∀ ρ,
    MarkedConstructorTargets.WholeWitness (domain F) F.data.sourceHeads M (ownerAt S F M Γ f ρ bs es)
      (MarkedConstructorTests.terms ts)

def CompleteObservation : Prop := ∀ S (F : Inputs S) Γ q t σ,
  WellFormed F.data.types F.data.ports Γ → Source F Γ q → Observed F Γ t →
  PaperTerm S q σ → PaperTerm S t σ →
  (Weak S q t → (FixedValue S F Γ q).weak Γ t = true) ∧
  (Strict S q t → (FixedValue S F Γ q).strict Γ t = true)

end LogicLineages.PersistentMarking.ProtectedSpineCompletenessTargets
