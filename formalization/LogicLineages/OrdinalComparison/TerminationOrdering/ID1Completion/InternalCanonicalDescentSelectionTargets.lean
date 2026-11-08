module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus
open InternalCanonicalDescentSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- On ORIGINAL source-valid inputs T is exactly R. Consequently its fixed
points there are precisely original R-fixed points. The proof must consume
original minimality/reflexivity and same-type valid representative/idempotence
results, not introduce these as new premises. This is EXTERNAL calibration. -/
def ActualOriginalCanonicalTransitionIdentification : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  Calibrated n arity symbols S Gamma table data →
  ∀ value : Nat,
  InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value = 1 →
    (evaluate (InternalBoundedDescentNormalizer.transition data.oldEdge.targetRepresentative
        (validity data).sourceValid) (List.Vector.ofFn ![value]) =
      evaluate data.oldEdge.targetRepresentative (List.Vector.ofFn ![value])) ∧
    (evaluate (InternalBoundedDescentNormalizer.transition data.oldEdge.targetRepresentative
        (validity data).sourceValid) (List.Vector.ofFn ![value]) = value ↔
      evaluate data.oldEdge.targetRepresentative (List.Vector.ofFn ![value]) = value)

/-- D agrees with the ORIGINAL packed-target representative on EVERY input.
The invalid-source branch remains R, including decoded nonuniverse terms;
it is not changed to zero. There is no valid-input premise on this equality. -/
def ActualOriginalCanonicalDescentCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  Calibrated n arity symbols S Gamma table data →
  ∀ v : List.Vector Nat 1,
    evaluate (representative data) v =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma (v.get 0)

/-- Exact equality to the original canonical typed carrier on ALL natural
[value,type] inputs, including malformed values and every requested type.
No old typed AST or opaque successful-run/fold-fixed conjunct is retained. -/
def ActualOriginalCanonicalDescentTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  Calibrated n arity symbols S Gamma table data →
  InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma (selectedTyped data)

/-- Both representative defaults, the literal old step, recursive validity
and exact original canonical typed carrier retain their full input domains. -/
def ActualOriginalCanonicalDescentDataCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data),
  SubtypeClosed (fun tau => tau ∈ S) →
  Calibrated n arity symbols S Gamma table data →
  SelectedCalibrated n arity symbols S Gamma table data

/-- Genuine internal iff for arbitrary original leaves and contexts. Raw
tag, source validity, membership and T-fixed graphs are all CONCLUSIONS of
acceptance; no external calibration or pre-supplied tag witness is assumed. -/
def ActualOriginalCanonicalDescentTypedFactorization : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid member : Program 1) (α : Type)
    (Delta : List (Formula α)) (value typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((typedAccepted representative valid member value typ).iff
      (typedFactors representative valid member value typ)))

/-- The actual D graph and exact-one input validity select B internally.
The checked arbitrary-leaf B validity theorem must be consumed, not assumed. -/
def ActualOriginalCanonicalDescentValidity : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Delta : List (Formula α)) (out input : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((representativeGraph representative valid out input).imp
      ((InternalBoundedDescentNormalizer.validGraph valid input).imp
        (InternalBoundedDescentNormalizer.validGraph valid out))))

/-- Input validity is essential for D: its fallback R need not preserve a
tag. Only exact graph premises appear, with no semantic source witness. -/
def ActualOriginalCanonicalDescentLeft : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Delta : List (Formula α)) (out input typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((representativeGraph representative valid out input).imp
      ((InternalBoundedDescentNormalizer.validGraph valid input).imp
        ((InternalBoundedDescentNormalizer.leftGraph typ input).imp
          (InternalBoundedDescentNormalizer.leftGraph typ out)))))

/-- The conclusion is T(out)=out, not D-fixed, B-fixed or R-fixed. Input
validity selects the B branch. No fixed-point premise is allowed. -/
def ActualOriginalCanonicalDescentFixedPoint : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid : Program 1) (α : Type)
    (Delta : List (Formula α)) (out input : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((representativeGraph representative valid out input).imp
      ((InternalBoundedDescentNormalizer.validGraph valid input).imp
        (InternalBoundedDescentNormalizer.transitionGraph representative valid out out))))

/-- Assemble the actual typed acceptance from D's graph, input validity,
input tag and requested-type membership. Output validity/tag/T-fixed are
proved internally from checked B, not inserted into the antecedent. -/
def ActualOriginalCanonicalDescentTypedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (representative valid member : Program 1) (α : Type)
    (Delta : List (Formula α)) (out input typ : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((outputPremises representative valid member out input typ).imp
      (typedAccepted representative valid member out typ)))

/-- ONE shared selection before every body, variable type, context, and term.
Only fixed subtype-closed windows are asserted. This is neither a context-
uniform compiler nor a fold, application-congruence, edge/path-lift or ID1
completion. No original canonicality condition is weakened to mere validity. -/
def ActualOriginalCanonicalDescentSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) →
  ∃ data : Data,
    Calibrated n arity symbols S Gamma table data ∧
      (SelectedCalibrated n arity symbols S Gamma table data ∧ InternalLaws data)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionTargets
