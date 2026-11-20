module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementObjectTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipObjectTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAuxBottomRefinementObjectTargets (packedAuxBottomTerm)
open NumberedWindowInternalAuxBottomMembership (augmented)

/-- At this exact new source body, a genuine carried certificate at a
bare bottom implies arithmetic falsum. At a literal bare-bottom-headed
auxiliary it yields the same actual whole-bottom output and its carrier.
The witness is the one in the original certificate adapter. -/
def ExactAugmentedTerminalCertificates : Prop :=
  (∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
      (Γ : List (Formula α)) (x w y ctx t : OTerm α),
    let S := data i j (augmented i r) d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (equal x (packedBottomTerm ctx t))) →
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ (⊥ : Formula α))) ∧
  (∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
      (Γ : List (Formula α)) (x w y ctx dom cod stored arg : OTerm α),
    let S := data i j (augmented i r) d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (equal x (packedAuxBottomTerm ctx dom cod stored arg))) →
    Nonempty (Derivation B Γ (certificate S false c x y w)) →
    Nonempty (Derivation B Γ (equal y (packedBottomTerm ctx cod) ⊓ carrier S false c y)))

/-- The actual I formula at the new source body. Shape alone is not
admission: the actual same input carrier remains explicit, and
membership implies it by the original rule. No auxiliary free head. -/
def ExactAugmentedBottomMembership : Prop :=
  (∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
      (Γ : List (Formula α)) (x ctx t : OTerm α),
    let S := data i j (augmented i r) d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (equal x (packedBottomTerm ctx t))) →
    (Nonempty (Derivation B Γ (carrier S false c x)) ↔
      Nonempty (Derivation B Γ (membership false x)))) ∧
  (∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
      (Γ : List (Formula α)) (x ctx dom cod stored arg : OTerm α),
    let S := data i j (augmented i r) d
    let B := sourceBody S c
    Nonempty (Derivation B Γ (equal x (packedAuxBottomTerm ctx dom cod stored arg))) →
    (Nonempty (Derivation B Γ (carrier S false c x)) ↔
      Nonempty (Derivation B Γ (membership false x))))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomMembershipObjectTargets
