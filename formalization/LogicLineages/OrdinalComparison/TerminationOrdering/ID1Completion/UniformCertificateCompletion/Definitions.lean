module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientEdgeCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data validity targetValidity)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Raw step inputs are [source,target,certificate,parameter]. The fourth
coordinate remains separate from every original certificate selector. -/
def validityAt (P : Program 2) (i : Fin 4) : Program 4 :=
  .composition P ![.projection i,.projection 3]

def sameOuterTypes : Program 4 :=
  InternalApplicationStepPeel.same (leftOf (.projection 0)) (leftOf (.projection 1))

def rawGuards (data : Data) : Program 4 :=
  InternalAcceptance.conjunction (validityAt (validity data) 0)
    (InternalAcceptance.conjunction (validityAt (targetValidity data) 1) sameOuterTypes)

/-- Exactly the old guarded normalized step, followed by the already-used
target source-validity check. That last check is redundant on original steps
in a subtype-closed window. It supplies the internal target fold invariant. -/
def stepChecker (data : Data) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction
    (InternalAcceptance.conjunction (rawGuards data)
      (InternalOriginalUniformApplicationStepSelection.selectedChecker data oldStep))
    (validityAt (validity data) 1)

/-- The original source-universe filter is retained. Its rejection default
is zero; the target representative below retains every packed target. -/
def sourceRepresentative (data : Data) : Program 2 :=
  InternalAcceptance.branch (InternalApplicationValidityStack.exactOne (validity data))
    (InternalAcceptance.constantZero 2) (InternalParameterizedCanonicalResultFold.foldN data)

def targetRepresentative (data : Data) : Program 2 :=
  InternalParameterizedCanonicalResultFold.foldN data

/-- Inputs [source endpoint,target endpoint,original certificate,parameter]. -/
def field (selector : Program 1) : Program 4 :=
  .composition selector (fun _ : Fin 1 => .projection 2)

def stepAt (data : Data) (oldStep : Program 4) : Program 4 :=
  .composition (stepChecker data oldStep)
    ![field source,field target,field step,.projection 3]

def representativeAt (representative : Program 2) (selector : Program 1) : Program 4 :=
  .composition representative ![field selector,.projection 3]

def representativeCheck (representative : Program 2) (selector : Program 1)
    (endpoint : Fin 4) : Program 4 :=
  InternalApplicationStepPeel.same (representativeAt representative selector) (.projection endpoint)

/-- One literal original quotient-edge checker at symbolic p. Its three
certificate fields, source filter, unfiltered target and endpoint equality
tests have the same meanings as the accepted fixed-window checker. -/
def edgeChecker (data : Data) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction (stepAt data oldStep)
    (InternalAcceptance.conjunction
      (representativeCheck (sourceRepresentative data) source 0)
      (representativeCheck (targetRepresentative data) target 1))

def stepAccepted {α : Type} (data : Data) (oldStep : Program 4)
    (s t k parameter : OTerm α) : Formula α :=
  graph4 (stepChecker data oldStep) InternalOriginalStepGuard.one s t k parameter

def edgeAccepted {α : Type} (data : Data) (oldStep : Program 4)
    (x y certificate parameter : OTerm α) : Formula α :=
  graph4 (edgeChecker data oldStep) InternalOriginalStepGuard.one x y certificate parameter

def requirements {α : Type} (data : Data) (oldStep : Program 4)
    (x y s t k parameter : OTerm α) : Formula α :=
  stepAccepted data oldStep s t k parameter ⊓
    (graph2 (sourceRepresentative data) x s parameter ⊓
      graph2 (targetRepresentative data) y t parameter)

def typedAccepted {α : Type} (data : Data)
    (x typ parameter : OTerm α) : Formula α :=
  InternalOriginalUniformDescentSelection.typedAccepted
    data.oldRepresentative (validity data) data.member x typ parameter

/-- This is all-input numeric calibration, not an internal reflection rule.
The same Data and oldStep precede every window and ambient Gamma. -/
def Calibrated (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun tau => tau ∈ S) → ∀ (x y certificate : Nat),
  evaluate (edgeChecker data oldStep) (List.Vector.ofFn
    ![x,y,certificate,InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table]) =
    (NumberedNumericQuotientEdge.numericEdgeTest n arity symbols S Gamma table
      x y certificate).toNat

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion
