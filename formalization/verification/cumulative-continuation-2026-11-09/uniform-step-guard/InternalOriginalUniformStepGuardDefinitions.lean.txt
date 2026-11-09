module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuard
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open InternalOriginalUniformParameterLeaves (parameterCode)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Inputs [raw source,raw target,raw step certificate,parameter]. Every
binary validity leaf receives its original value and the unchanged parameter. -/
def atParameter (P : Program 2) (i : Fin 4) : Program 4 :=
  .composition P ![.projection i,.projection 3]

/-- The same original numeric outer-type comparison, at arity four. The
extra parameter is not part of either raw term or its original type code. -/
def sameOuterTypes : Program 4 :=
  InternalApplicationStepPeel.same (leftOf (.projection 0)) (leftOf (.projection 1))

def guards (sourceValid targetValid : Program 2) : Program 4 :=
  InternalAcceptance.conjunction (atParameter sourceValid 0)
    (InternalAcceptance.conjunction (atParameter targetValid 1) sameOuterTypes)

/-- The original source-universe, packed-target and equal-raw-type guards
surround the supplied actual Program4. Every conjunct accepts exactly at one. -/
def guardedChecker (sourceValid targetValid : Program 2) (core : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (guards sourceValid targetValid) core

/-- The selected core is the already checked actual endpoint/peel/repeat
construction. Data and oldStep are used literally without new fields. -/
def guardedStep (data : Data) (oldStep : Program 4) : Program 4 :=
  guardedChecker (validity data) (targetValidity data)
    (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)

def targetSourceValidityAt (data : Data) : Program 4 :=
  atParameter (validity data) 1

/-- W is exactly guardedStep AND original SOURCE validity at the raw target.
This strengthens the accepted step graph, not the target representative's
all-input function. No canonical result, success or alternate endpoint is
inserted into the raw source/target/certificate triple. -/
def stepChecker (data : Data) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (guardedStep data oldStep) (targetSourceValidityAt data)

def guardedAccepted {α : Type} (sourceValid targetValid : Program 2) (core : Program 4)
    (s t k parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph4 (guardedChecker sourceValid targetValid core) InternalOriginalStepGuard.one s t k parameter

/-- A source tag is supplied independently. The target tag is an output
of the internal factorization, alongside both original validity factors. -/
def taggedRequirements {α : Type} (sourceValid targetValid : Program 2) (core : Program 4)
    (tag s t k parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 sourceValid InternalOriginalStepGuard.one s parameter ⊓
    (graph2 targetValid InternalOriginalStepGuard.one t parameter ⊓
      (graph1 InternalUnpair.left tag t ⊓ graph4 core InternalOriginalStepGuard.one s t k parameter))

def stepAccepted {α : Type} (data : Data) (oldStep : Program 4)
    (s t k parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph4 (stepChecker data oldStep) InternalOriginalStepGuard.one s t k parameter

/-- W exposes source validity at BOTH raw endpoints. Packed target validity,
its source-matching raw tag and the original selected core acceptance remain
explicit. No supplied target tag or decoded object is required. -/
def stepRequirements {α : Type} (data : Data) (oldStep : Program 4)
    (tag s t k parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (validity data) InternalOriginalStepGuard.one s parameter ⊓
    (graph2 (validity data) InternalOriginalStepGuard.one t parameter ⊓
      (graph2 (targetValidity data) InternalOriginalStepGuard.one t parameter ⊓
        (graph1 InternalUnpair.left tag t ⊓
          graph4 (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep)
            InternalOriginalStepGuard.one s t k parameter)))

/-- The original arrow and selected endpoint graphs, both original raw
applications, and original stepLift. Neither lifted validity nor lifted
checker acceptance is a premise. The endpoint retains packed target validity. -/
def liftPremises {α : Type} (data : Data)
    (arrow d e s t a k sourceApp targetApp liftedStep parameter : OrdinaryArithmetic.Term α) : Formula α :=
  InternalParameterizedStructuralEndpointGuard.applicationPremises
      data arrow d e s t a sourceApp targetApp parameter ⊓
    graph1 stepLift liftedStep k

/-- All raw inputs at every original context slice, without a closure
condition on the finite type window. -/
def GuardedCalibrated (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    InternalParameterizedApplicationStepChecker.StepCalibratedAt n arity symbols S Gamma table
      (guardedStep data oldStep) (parameterCode symbols S Gamma table)

/-- W retains every raw input of the original numeric step function at
subtype-closed windows. Closure supplies the redundancy of V(raw target). -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun typ => typ ∈ S) →
    InternalParameterizedApplicationStepChecker.StepCalibratedAt n arity symbols S Gamma table
      (stepChecker data oldStep) (parameterCode symbols S Gamma table)

/-- These are conclusions about the same literal selected W, not Data
fields or supplied derivability rules. All parameters stay symbolic. -/
def InternalLaws (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)),
    (∀ (tag s t k parameter : OrdinaryArithmetic.Term α),
      Nonempty (Derivation body Delta
        ((graph1 InternalUnpair.left tag s).imp
          ((stepAccepted data oldStep s t k parameter).iff
            (stepRequirements data oldStep tag s t k parameter))))) ∧
    (∀ (arrow d e s t a k sourceApp targetApp liftedStep parameter : OrdinaryArithmetic.Term α),
      Nonempty (Derivation body Delta
        ((liftPremises data arrow d e s t a k sourceApp targetApp liftedStep parameter ⊓
          stepAccepted data oldStep s t k parameter).imp
          (stepAccepted data oldStep sourceApp targetApp liftedStep parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuard
