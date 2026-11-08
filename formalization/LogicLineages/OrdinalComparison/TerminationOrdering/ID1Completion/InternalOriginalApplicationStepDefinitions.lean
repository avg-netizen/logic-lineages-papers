module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStep
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only finite original Program leaves. There is no correctness, closure,
typing, lift or derivability field. All constructed wrappers below share
these exact leaves, selected before any internal body or symbolic term. -/
structure Data where
  oldValidity : InternalOriginalStepGuard.Data
  member : Program 1
  oldStep : Program 3

/-- The selected validity is the concrete bounded recursive AST, not an
arbitrary existentially calibrated replacement. Its source is the conjunction
of target validation and universe validation; target has no universe filter. -/
def validity (data : Data) : InternalOriginalStepGuard.Data :=
  InternalApplicationValidityStack.recursiveData data.oldValidity data.member

def endpoint (data : Data) : Program 5 :=
  InternalStructuralEndpointGuard.endpoint (validity data) data.member

def normalizedCore (data : Data) : Program 3 :=
  InternalApplicationStepPeel.checker (endpoint data) data.oldStep

/-- The outer original validity/type guard is retained around the SAME
normalized core at original and lifted source/target/certificate inputs. -/
def stepChecker (data : Data) : Program 3 :=
  InternalOriginalStepGuard.checker (validity data) (normalizedCore data)

/-- Every leaf calibration covers all natural inputs at fixed original
signature, window and Gamma. These are external equalities only. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma data.oldValidity ∧
    (InternalStructuralEndpointGuard.MembershipCalibrated S data.member ∧
      InternalApplicationStepChecker.StepCalibrated n arity symbols S Gamma table data.oldStep)

/-- The exact constructed recursive validity, endpoint and guarded step
retain the entire original functions, including malformed raw inputs.
No semantic equality is used to identify internal graph predicates. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma (validity data) ∧
    (InternalApplicationStepPeel.EndpointCalibrated n arity symbols S Gamma (endpoint data) ∧
      InternalApplicationStepChecker.StepCalibrated n arity symbols S Gamma table (stepChecker data))

def accepted {α : Type} (data : Data)
    (s t k : OrdinaryArithmetic.Term α) : Formula α :=
  graph3 (stepChecker data) InternalOriginalStepGuard.one s t k

/-- Actual arrow, accepted endpoint, both original raw application graphs,
and the unchanged original certificate lift. The endpoint supplies all child
tags and child validities; neither lifted validity nor lifted acceptance is
assumed. The arbitrary original certificate k is not restricted or decoded. -/
def liftPremises {α : Type} (data : Data)
    (arrow d e s t a k sourceApp targetApp liftedStep : OrdinaryArithmetic.Term α) : Formula α :=
  InternalApplicationValidityClosure.endpointApplicationPremises
      data.oldValidity data.member arrow d e s t a sourceApp targetApp ⊓
    graph1 stepLift liftedStep k

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStep
