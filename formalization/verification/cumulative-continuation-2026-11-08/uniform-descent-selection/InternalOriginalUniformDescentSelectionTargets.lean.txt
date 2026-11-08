module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalOriginalUniformDescentSelection
open InternalOriginalUniformParameterLeaves (parameterCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The SAME globally calibrated leaves feed the actual parameterized result
validators. Every raw value is included; no closed-window hypothesis is needed. -/
def ActualOriginalUniformValidityCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data), Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (value : Nat),
    evaluate (targetValidity data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalOriginalStepGuard.targetValidityValue n arity Gamma value ∧
    evaluate (validity data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value

/-- Original least-code minimality, same-type validity and idempotence must
prove this transition identification. They are not additional data fields. -/
def ActualOriginalUniformTransitionIdentification : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data), Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) → ∀ value : Nat,
    InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma value = 1 →
    evaluate (InternalParameterizedBoundedDescentNormalizer.transition data.oldRepresentative (validity data))
      (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value

/-- Original packed-target representative on EVERY natural value, including
malformed values and decoded nonuniverse terms. Invalid-source fallback is R. -/
def ActualOriginalUniformRepresentativeCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data), Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) → ∀ value : Nat,
    evaluate (representative data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value

/-- One ternary AST, selected before every window and Gamma, is exactly the
original canonical typed carrier at every raw value and requested type code. -/
def ActualOriginalUniformTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data), Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) → ∀ value typ : Nat,
    evaluate (selectedTyped data) (List.Vector.ofFn ![value,typ,parameterCode symbols S Gamma table]) =
      InternalOriginalTypedCarrier.typedValue n arity symbols S Gamma (List.Vector.ofFn ![value,typ])

/-- Internal iff for arbitrary binary leaves and arbitrary symbolic p.
All four original graph factors follow from the actual checker acceptance. -/
def ActualParameterizedTypedFactorization : Prop :=
  ∀ (body : Positive (Fin 1)) (R V member : Program 2) (α : Type)
    (Delta : List (Formula α)) (value typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((typedAccepted R V member value typ parameter).iff
      (typedFactors R V member value typ parameter)))

/-- Only actual D, input-validity and original input-tag graphs are supplied.
Output validity, original tag and transition fixedness are derived internally. -/
def ActualParameterizedRepresentativeInvariant : Prop :=
  ∀ (body : Positive (Fin 1)) (R V : Program 2) (α : Type)
    (Delta : List (Formula α)) (out input typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((outputPremises R V out input typ parameter).imp
      (outputInvariant R V out typ parameter)))

/-- Requested-type membership remains explicit; arbitrary V has no internal
type-membership law. No semantic calibration or source decode is a premise. -/
def ActualParameterizedTypedOutput : Prop :=
  ∀ (body : Positive (Fin 1)) (R V member : Program 2) (α : Type)
    (Delta : List (Formula α)) (out input typ parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((typedOutputPremises R V member out input typ parameter).imp
      (typedAccepted R V member out typ parameter)))

/-- The exact source conjunction closes under the original raw application
constructor, deriving both validator branches at the unchanged parameter. -/
def ActualParameterizedSourceApplicationClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type) (Delta : List (Formula α))
    (arrow d e fp ap fn arg parent parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Delta
    ((applicationPremises data arrow d e fp ap fn arg parent parameter).imp
      (graph2 (validity data) InternalOriginalStepGuard.one parent parameter)))

/-- ONE actual four-leaf tuple is selected after n/arity and BEFORE symbols,
S, Gamma, table, body and all symbolic terms. Calibration and every internal
law are conclusions. There is no supplied PR/leaf/calibration/closure premise.
This is uniform descent and canonical typing; the canonical result fold and
unqualified CertifiedApplicationLift remain separate source obligations. -/
def ActualOriginalUniformDescentSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : Data,
    Calibrated n arity data ∧ InternalLaws data ∧
    ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
      SubtypeClosed (fun tau => tau ∈ S) → SelectedCalibrated n arity symbols S Gamma table data

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionTargets
