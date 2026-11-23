module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultisetTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowInternalAccessibilityTargets (Rules)

/-- Select a concrete direct checker rejecting packed-empty source in a
literal zero branch. The earlier direct program is unchanged on nonzero codes. -/
def emptyGuard (d : Program 3) : Program 3 :=
  branch (.projection 0) (constantZero 3) d

def ExactDirectSelection : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d → Evaluates (checks xs s) i j r (emptyGuard d)

/-- Refute the actual accepting certificate with arbitrary object successor
and witness on this exact source body, not just its numeral instances. -/
def ExactOpenEmptyCertificateRejection : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (y w : OrdinaryArithmetic.Term α),
    let S := data i j r (emptyGuard d)
    Nonempty (Derivation (sourceBody S c) Γ (certificate S true c OrdinaryArithmetic.zeroTerm y w)) →
    Nonempty (Derivation (sourceBody S c) Γ (⊥ : Formula α))

def ExactSelectedEmptyMultiset : Prop :=
  ∀ (xs : Entries) (s : Settings), ∃ (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d ∧
    Evaluates (checks xs s) i j r (emptyGuard d) ∧
    let S := data i j r (emptyGuard d)
    Interprets (checks xs s) S ∧ Rules S ∧
    ∀ (c : Nat) (α : Type) (Γ : List (Formula α)),
      Nonempty (Derivation (sourceBody S c) Γ (membership true (OrdinaryArithmetic.zeroTerm : OrdinaryArithmetic.Term α)))

end LogicLineages.PersistentMarking.NumberedWindowInternalEmptyMultisetTargets
