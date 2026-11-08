module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalCanonicalQuotientEdgeSelection

/-- The new V(raw target) conjunct is redundant on accepted ORIGINAL steps
at a subtype-closed window. Every natural input is covered, including failed
decodes; no semantic acceptance or successful decode is a target premise. -/
def ActualOriginalCanonicalEdgeStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  InternalApplicationStepChecker.StepCalibrated n arity symbols S Gamma table
    (stepChecker data)

/-- The SAME updated step leaf sits under the existing N representatives.
Recursive validity, canonical typed carrier and final quotient-edge checker
retain their original all-input functions, including distinct source/target
defaults. R/V/D/T/C/N/H and typed syntax have not been replaced. -/
def ActualOriginalCanonicalEdgeDataCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data →
  SelectedCalibrated n arity symbols S Gamma table data

/-- Internal closure of the EXACT selected W at raw applications. Existing
liftPremises are unchanged, and only W(s,t,k) is additionally assumed. The
target V(application) conjunct must be derived from W's V(t), the endpoint
graphs and the actual recursive validity rules. No H, old typed checker,
calibration, semantic reflection or new closure premise is permitted. -/
def ActualOriginalCanonicalEdgeApplicationStep : Prop :=
  ∀ (body : Positive (Fin 1)) (data : InternalCanonicalDescentSelection.Data)
    (α : Type) (Delta : List (Formula α))
    (arrow d e s t a k sourceApp targetApp liftedStep : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((InternalOriginalApplicationStep.liftPremises (baseData data)
        arrow d e s t a k sourceApp targetApp liftedStep ⊓
      stepAccepted data s t k).imp
      (stepAccepted data sourceApp targetApp liftedStep)))

/-- Genuine internal propagation at the SAME final quotient-edge checker
and canonical typed AST. typ is an arbitrary symbolic term, not a numeral
of an externally supplied type. Only typed(x,typ) and edge(x,y,certificate)
are premises. Raw certificate selectors, tags, validities and fold outputs
must be recovered internally; membership comes from typed(x,typ). There is
no calibration, subtype closure, separate membership, old typed or H premise. -/
def ActualOriginalCanonicalEdgeTypedPropagation : Prop :=
  ∀ (body : Positive (Fin 1)) (data : InternalCanonicalDescentSelection.Data)
    (α : Type) (Delta : List (Formula α))
    (x y certificate typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((typedAccepted data x typ ⊓ edgeAccepted data x y certificate).imp
      (typedAccepted data y typ)))

/-- ONE existing canonical descent Data is selected before every body,
variable type, derivation context, symbolic type, endpoint and certificate.
Both internal laws use the exact externally calibrated W/edge/typed ASTs.
This is not an application quotient-edge lift, path lift, context-uniform
compiler, CertifiedApplicationLift or completion of paper06 lem:id1. -/
def ActualOriginalCanonicalEdgeSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∃ data : InternalCanonicalDescentSelection.Data,
    InternalCanonicalDescentSelection.Calibrated n arity symbols S Gamma table data ∧
      (SelectedCalibrated n arity symbols S Gamma table data ∧ InternalLaws data)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionTargets
