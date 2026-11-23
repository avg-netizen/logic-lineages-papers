module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAccessibilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranchTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalControlGraph (equal)
open ID1Completion.InternalAcceptance (branch constantZero)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowInternalSingletonBottomTargets (recognize packedSingletonBottom)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowFormulaCalibrationTargets (Evaluates)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

def sourceSelector : Program 3 :=
  .composition recognize (fun _ => .projection (0 : Fin 3))

def sourceControl : Program 3 := GorbowVerifierNormalization.normalize sourceSelector

def targetBranch (d : Program 3) : Program 3 :=
  branch (.projection 2) d (constantZero 3)

/-- On the singleton-bottom branch only, require the literal zero target.
Every input that reaches the original direct checker keeps its exact value. -/
def singletonGuard (d : Program 3) : Program 3 :=
  branch sourceControl d (targetBranch d)

def ExactSingletonGuardSelection : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d → Evaluates (checks xs s) i j r (singletonGuard d)

def ExactSymbolicSingletonCertificateTarget : Prop :=
  ∀ (i j : Program 1) (r d : Program 3) (c : Nat) (α : Type)
    (Γ : List (Formula α)) (ctx t y w : OrdinaryArithmetic.Term α),
    let S := data i j r (singletonGuard d)
    let B := sourceBody S c
    Nonempty (Derivation B Γ (certificate S true c (packedSingletonBottom ctx t) y w)) →
    Nonempty (Derivation B Γ (equal y OrdinaryArithmetic.zeroTerm))

end LogicLineages.PersistentMarking.NumberedWindowInternalSingletonBottomBranchTargets
