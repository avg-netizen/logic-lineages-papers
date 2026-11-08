module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelection
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Reuse the existing canonical descent Data without adding any field.
The original application-step wrapper receives these SAME three leaves. -/
def baseData (data : InternalCanonicalDescentSelection.Data) :
    InternalOriginalApplicationStep.Data where
  oldValidity := data.oldValidity
  member := data.member
  oldStep := data.oldEdge.stepProgram

/-- Inputs are [raw source, raw target, raw step certificate]. V is the
unchanged recursive SOURCE validity, now applied to the raw target. -/
def targetSourceValidityAt (data : InternalCanonicalDescentSelection.Data) : Program 3 :=
  .composition (InternalCanonicalDescentSelection.validity data).sourceValid
    (fun _ : Fin 1 => .projection 1)

/-- W has exactly TWO conjuncts: the actual original guarded application
step and V(raw target). There is no H guard, old typed checker, successful
fold-run premise, endpoint replacement, or additional application wrapper. -/
def stepChecker (data : InternalCanonicalDescentSelection.Data) : Program 3 :=
  InternalAcceptance.conjunction
    (InternalOriginalApplicationStep.stepChecker (baseData data))
    (targetSourceValidityAt data)

/-- Update ONLY oldEdge.stepProgram to W. In particular the original R,
recursive V, D, T, C, N, H and selected typed checker remain definitionally
unchanged. No existing Data interface or accepted definition is edited. -/
def selectedData (data : InternalCanonicalDescentSelection.Data) :
    InternalCanonicalDescentSelection.Data :=
  { data with oldEdge := { data.oldEdge with stepProgram := stepChecker data } }

/-- The existing fold-edge constructor sees the updated step leaf. Source
is N when V accepts and zero otherwise; target remains N on EVERY input. -/
def edgeData (data : InternalCanonicalDescentSelection.Data) : InternalQuotientEdgeChecker.Data :=
  InternalCanonicalResultFoldCalibration.edgeData (selectedData data)

/-- The actual existing quotient-edge checker, with its original certificate
selectors and equality tests. No new certificate encoding or path checker. -/
def edgeChecker (data : InternalCanonicalDescentSelection.Data) : Program 3 :=
  InternalQuotientEdgeChecker.checker (edgeData data)

def stepAccepted {α : Type} (data : InternalCanonicalDescentSelection.Data)
    (s t k : OrdinaryArithmetic.Term α) : Formula α :=
  graph3 (stepChecker data) InternalOriginalStepGuard.one s t k

def edgeAccepted {α : Type} (data : InternalCanonicalDescentSelection.Data)
    (x y certificate : OrdinaryArithmetic.Term α) : Formula α :=
  InternalQuotientEdgeChecker.accepted (edgeData data) x y certificate

/-- Literal canonical descent typed acceptance at the unchanged R/V/member
leaves. Requested type remains an arbitrary symbolic arithmetic term. -/
def typedAccepted {α : Type} (data : InternalCanonicalDescentSelection.Data)
    (value typ : OrdinaryArithmetic.Term α) : Formula α :=
  InternalCanonicalDescentSelection.typedAccepted data.oldEdge.targetRepresentative
    (InternalCanonicalDescentSelection.validity data).sourceValid data.member value typ

/-- External all-natural-input calibration of W, the existing fold-edge
data and typed carrier, and the actual final quotient-edge checker. The
unchanged leaf calibration is separately required by the selection target. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data) : Prop :=
  InternalApplicationStepChecker.StepCalibrated n arity symbols S Gamma table
      (stepChecker data) ∧
    (InternalCanonicalResultFoldCalibration.SelectedCalibrated
        n arity symbols S Gamma table (selectedData data) ∧
      ∀ v : List.Vector Nat 3,
        evaluate (edgeChecker data) v =
          (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
            (v.get 0) (v.get 1) (v.get 2)).toNat)

/-- Two properties of ONE fixed selection, not Data fields or assumed
suppliers. No calibration, membership, raw selector/tag/validity, H or typed
target premise is added to typed propagation. Internal certificate witnesses
must be obtained from the actual original Programs. -/
def InternalLaws (data : InternalCanonicalDescentSelection.Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)),
    (∀ (arrow d e s t a k sourceApp targetApp liftedStep : OrdinaryArithmetic.Term α),
      Nonempty (Derivation body Delta
        ((InternalOriginalApplicationStep.liftPremises (baseData data)
            arrow d e s t a k sourceApp targetApp liftedStep ⊓
          stepAccepted data s t k).imp
          (stepAccepted data sourceApp targetApp liftedStep)))) ∧
    (∀ (x y certificate typ : OrdinaryArithmetic.Term α),
      Nonempty (Derivation body Delta
        ((typedAccepted data x typ ⊓ edgeAccepted data x y certificate).imp
          (typedAccepted data y typ))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelection
