module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranchTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultisetTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSingletonBottomTargets (packedSingletonBottom)
open NumberedWindowInternalSingletonBottomBranchTargets (singletonGuard)
open NumberedWindowInternalEmptyMultisetTargets (emptyGuard)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

/-- Both branches are part of this literal new direct checker. -/
def selectedDirect (d : Program 3) : Program 3 := singletonGuard (emptyGuard d)

/-- On a fresh same-body selection, derive J(0), and derive J of the
literal packed singleton bottom from its actual same-body carrier.
The latter carrier remains an explicit open derivability premise. -/
def ExactSelectedSingletonBottomMembership : Prop :=
  ∀ (xs : Entries) (s : Settings), ∃ (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d ∧
    Evaluates (checks xs s) i j r (selectedDirect d) ∧
    let S := data i j r (selectedDirect d)
    Interprets (checks xs s) S ∧ Rules S ∧
    ∀ (c : Nat) (α : Type) (Γ : List (Formula α)),
      let B := sourceBody S c
      Nonempty (Derivation B Γ (membership true (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term α))) ∧
      ∀ ctx t : OrdinaryArithmetic.Term α,
        Nonempty (Derivation B Γ (carrier S true c (packedSingletonBottom ctx t))) →
        Nonempty (Derivation B Γ (membership true (packedSingletonBottom ctx t)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomMembershipTargets
