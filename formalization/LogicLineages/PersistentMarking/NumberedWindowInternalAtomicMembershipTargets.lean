module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (packedFreeTerm)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)

/-- The actual original universal successor premise of I. No witness
is assumed or fabricated. The bottom case rules out the genuine
existential certificate; a free descendant has the same bottom
shape and same actual scalar carrier under the new body. -/
def ExactRefinedAtomicSuccessors : Prop :=
  (∀ (i j : Program 1) (r d : Program 3) (context : Nat) (α : Type)
      (Γ : List (Formula α)) (x c t : OTerm α),
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (equal x (packedBottomTerm c t))) →
    Nonempty (Derivation B Γ (successors S false context x))) ∧
  (∀ (i j : Program 1) (r d : Program 3) (context : Nat) (α : Type)
      (Γ : List (Formula α)) (x c t n : OTerm α),
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (equal x (packedFreeTerm c t n))) →
    Nonempty (Derivation B Γ (successors S false context x)))

/-- Atomic I with exactly the original carrier premise on this same x
and actual new sourceBody. Shape alone does not establish a carrier.
This is a statement about derivations, not external numerical
accessibility or C at an arbitrary arrow type. -/
def ExactRefinedAtomicMembership : Prop :=
  (∀ (i j : Program 1) (r d : Program 3) (context : Nat) (α : Type)
     (Γ : List (Formula α)) (x c t : OTerm α),
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (equal x (packedBottomTerm c t))) →
    (Nonempty (Derivation B Γ (carrier S false context x)) ↔
      Nonempty (Derivation B Γ (membership false x)))) ∧
  (∀ (i j : Program 1) (r d : Program 3) (context : Nat) (α : Type)
      (Γ : List (Formula α)) (x c t n : OTerm α),
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (equal x (packedFreeTerm c t n))) →
    (Nonempty (Derivation B Γ (carrier S false context x)) ↔
      Nonempty (Derivation B Γ (membership false x))))

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
