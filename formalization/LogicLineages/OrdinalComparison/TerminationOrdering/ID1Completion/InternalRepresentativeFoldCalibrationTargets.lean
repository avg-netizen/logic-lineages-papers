module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationTargets
open Source InternalRepresentativeFoldCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Independent payload-recursive semanticFold equals the ORIGINAL packed-
target representative on every raw input. Subtype closure is used only for
original representative application congruence at a source-valid opened root.
Nonapplications, nonuniverse terms and malformed inputs keep the exact old
target behavior. There is no successful-decoding premise on the input. -/
def ActualOriginalSemanticRepresentativeFoldCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  InternalStructuralEndpointGuard.MembershipCalibrated S member →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old →
  ∀ value : Nat,
  InternalApplicationResultFoldCalibration.semanticFold
    (fun x => evaluate (rootGuard validity member) (List.Vector.ofFn ![x]))
    (fun x => evaluate (leaf validity member old) (List.Vector.ofFn ![x]))
    (fun d e f a => evaluate (combine old) (List.Vector.ofFn ![d,e,f,a])) value =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value

/-- Calibration of the ACTUAL finite fold and the explicit source/target
selection, with the old step AST unchanged. The generic all-input fold
calibration must be consumed as a proved supplier, not added as a hypothesis.
This is external natural-number calibration, not internal graph congruence. -/
def ActualOriginalRepresentativeFoldProgramCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  InternalStructuralEndpointGuard.MembershipCalibrated S member →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table
    (foldedData validity member old)

/-- For EACH fixed original window, calibrated programs can be selected with
literal foldedData on subtype-closed windows and literal old Data otherwise.
This is an existential fixed-window selection, NOT a uniform computable
compiler or a recursive-fold calibration claim for bad windows. -/
def ActualOriginalFixedWindowRepresentativeSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  InternalStructuralEndpointGuard.MembershipCalibrated S member →
  InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table old →
  ∃ data : InternalQuotientEdgeChecker.Data,
    InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table data ∧
    (SubtypeClosed (fun tau => tau ∈ S) → data = foldedData validity member old) ∧
    (¬ SubtypeClosed (fun tau => tau ∈ S) → data = old)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationTargets
