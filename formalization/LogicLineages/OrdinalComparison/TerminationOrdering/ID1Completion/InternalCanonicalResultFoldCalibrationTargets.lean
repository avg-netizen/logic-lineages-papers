module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationTargets
open Source InternalCanonicalResultFoldCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The COMPLETE tag-2 opening decisions agree on every raw input. This is
not G=V outside applications. Original sourceAppAcceptance must recover both
original child-universe facts and codomain membership in the open case. -/
def ActualOriginalCanonicalFoldOpeningCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ∀ v : List.Vector Nat 1,
    evaluate (InternalApplicationResultStack.openGuard (rootGuard data)) v =
      evaluate (InternalApplicationResultStack.openGuard
        (InternalCanonicalDescentSelection.validity data).sourceValid) v

/-- D and D(rawApp) preserve the ORIGINAL target representative on their
entire raw domains. In the second equation neither child output has a validity,
type, canonicality or universe premise. This is not codomain repacking. -/
def ActualOriginalCanonicalFoldLeafCombineCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  (∀ v : List.Vector Nat 1,
    evaluate (leaf data) v =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
        (v.get 0)) ∧
  (∀ v : List.Vector Nat 4,
    evaluate (combine data) v =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
        (ApplicationCertificateLift.applicationValue v))

/-- Independent original-payload recursion at the EXACT G/D/D(rawApp) leaves
equals the original packed-target representative on EVERY natural input.
Application congruence must be proved using the original quotient theorem,
not assumed as a new calibration field or borrowed from the old combine. -/
def ActualOriginalSemanticCanonicalFoldCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ∀ value : Nat,
  InternalApplicationResultFoldCalibration.semanticFold
    (fun x => evaluate (rootGuard data) (List.Vector.ofFn ![x]))
    (fun x => evaluate (leaf data) (List.Vector.ofFn ![x]))
    (fun d e f a => evaluate (combine data) (List.Vector.ofFn ![d,e,f,a])) value =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value

/-- The ACTUAL finite N returns the original target representative and the
ACTUAL H returns one on all raw inputs. Generic fold calibration and singleton
success are checked suppliers to consume, not new hypotheses. Malformed and
decoded nonuniverse inputs are included, with no input canonicality premise. -/
def ActualOriginalCanonicalFoldProgramCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  ∀ v : List.Vector Nat 1,
    evaluate (normalizer data) v =
        InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma
          (v.get 0) ∧
      evaluate (goodRun data) v = 1

/-- At the SAME old leaves, finite window and Gamma, keep the old step,
recursive source/target validity and original canonical typed checker while
using N for target and source-guarded N for source. Every component retains
its original all-input calibration, including the two different defaults. -/
def ActualOriginalCanonicalFoldDataCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  SelectedCalibrated n arity symbols S Gamma table data

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationTargets
