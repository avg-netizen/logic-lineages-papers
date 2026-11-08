module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelection
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- D(x) uses B(x) exactly when V(x)=1. Every other output of V selects the
ORIGINAL R(x), preserving its behavior on malformed and nonuniverse inputs.
The original branch argument order is control, zero branch, nonzero branch. -/
def fallbackRepresentative (representative valid : Program 1) : Program 1 :=
  InternalAcceptance.branch (InternalApplicationValidityStack.exactOne valid)
    representative (InternalBoundedDescentNormalizer.normalizer representative valid)

/-- Inputs remain [value,type]. This is a composition of the actual V leaf. -/
def validAt (valid : Program 1) : Program 2 :=
  .composition valid (fun _ : Fin 1 => .projection 0)

/-- Actual equality-test AST for T(value)=value, not R-fixed or B-fixed. -/
def transitionFixed (representative valid : Program 1) : Program 2 :=
  InternalApplicationStepPeel.same
    (.composition (InternalBoundedDescentNormalizer.transition representative valid)
      (fun _ : Fin 1 => .projection 0)) (.projection 0)

/-- Exactly validity, the ORIGINAL raw left tag, and T-fixed. There is no
old typed checker, successful fold-run checker, or fold-fixed conjunct. -/
def typedCore (representative valid : Program 1) : Program 2 :=
  InternalAcceptance.conjunction (validAt valid)
    (InternalAcceptance.conjunction InternalOriginalTypedCarrier.sameOuterType
      (transitionFixed representative valid))

/-- The membership coordinate is the REQUESTED type, not the value. -/
def membershipAt (member : Program 1) : Program 2 :=
  .composition member (fun _ : Fin 1 => .projection 1)

/-- Expose type membership for endpoint consumers. Its redundancy on the
original canonical carrier must be proved externally on all natural inputs. -/
def typedChecker (representative valid member : Program 1) : Program 2 :=
  InternalAcceptance.conjunction (membershipAt member) (typedCore representative valid)

/-- A separate minimal selection interface. Only original finite Program
leaves are stored; no old typed AST, correctness, fixed-point or lift field. -/
structure Data where
  oldValidity : InternalOriginalStepGuard.Data
  member : Program 1
  oldEdge : InternalQuotientEdgeChecker.Data

def validity (data : Data) : InternalOriginalStepGuard.Data :=
  InternalApplicationValidityStack.recursiveData data.oldValidity data.member

/-- R is literally the old packed-target representative, without a new
universe restriction. V is literally the checked recursive SOURCE validity. -/
def representative (data : Data) : Program 1 :=
  fallbackRepresentative data.oldEdge.targetRepresentative (validity data).sourceValid

def selectedTyped (data : Data) : Program 2 :=
  typedChecker data.oldEdge.targetRepresentative (validity data).sourceValid data.member

/-- Keep the old step AST. Source is D on source-valid inputs and zero
otherwise; target is D on EVERY input. No endpoint/path guard is inserted. -/
def edgeData (data : Data) : InternalQuotientEdgeChecker.Data where
  stepProgram := data.oldEdge.stepProgram
  sourceRepresentative := InternalAcceptance.branch
    (InternalApplicationValidityStack.exactOne (validity data).sourceValid)
    (InternalAcceptance.constantZero 1) (representative data)
  targetRepresentative := representative data

/-- External all-input calibration of the shared original leaves only. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma data.oldValidity ∧
    (InternalStructuralEndpointGuard.MembershipCalibrated S data.member ∧
      InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table data.oldEdge)

/-- Three unchanged external interfaces, all quantified over every natural
input. No equality of internal graph formulas is inferred from this record. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma (validity data) ∧
    (InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table (edgeData data) ∧
      InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma (selectedTyped data))

def representativeGraph {α : Type} (representative valid : Program 1)
    (out input : OrdinaryArithmetic.Term α) : Formula α :=
  InternalBoundedDescentNormalizer.unaryGraph
    (fallbackRepresentative representative valid) out input

def typedAccepted {α : Type} (representative valid member : Program 1)
    (value typ : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (typedChecker representative valid member) InternalOriginalStepGuard.one value typ

/-- All four conjuncts are actual original arithmetic graphs. No externally
true validity, tag, fixed point or membership is supplied as an internal rule. -/
def typedFactors {α : Type} (representative valid member : Program 1)
    (value typ : OrdinaryArithmetic.Term α) : Formula α :=
  InternalBoundedDescentNormalizer.unaryGraph member InternalOriginalStepGuard.one typ ⊓
    (InternalBoundedDescentNormalizer.validGraph valid value ⊓
      (InternalBoundedDescentNormalizer.leftGraph typ value ⊓
        InternalBoundedDescentNormalizer.transitionGraph representative valid value value))

/-- Exact graph-only premises sufficient to produce a typed output of D.
Membership remains a premise because arbitrary V carries no internal type law. -/
def outputPremises {α : Type} (representative valid member : Program 1)
    (out input typ : OrdinaryArithmetic.Term α) : Formula α :=
  representativeGraph representative valid out input ⊓
    (InternalBoundedDescentNormalizer.validGraph valid input ⊓
      (InternalBoundedDescentNormalizer.leftGraph typ input ⊓
        InternalBoundedDescentNormalizer.unaryGraph member InternalOriginalStepGuard.one typ))

/-- A property of the fixed selection, NOT a Data field or assumed supplier.
The shared leaves precede every body, variable type, context and symbolic term. -/
def InternalLaws (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)),
    (∀ (value typ : OrdinaryArithmetic.Term α), Nonempty (Derivation body Delta
      ((typedAccepted data.oldEdge.targetRepresentative (validity data).sourceValid
          data.member value typ).iff
        (typedFactors data.oldEdge.targetRepresentative (validity data).sourceValid
          data.member value typ)))) ∧
    (∀ (out input typ : OrdinaryArithmetic.Term α), Nonempty (Derivation body Delta
      ((outputPremises data.oldEdge.targetRepresentative (validity data).sourceValid
          data.member out input typ).imp
        (typedAccepted data.oldEdge.targetRepresentative (validity data).sourceValid
          data.member out typ))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelection
