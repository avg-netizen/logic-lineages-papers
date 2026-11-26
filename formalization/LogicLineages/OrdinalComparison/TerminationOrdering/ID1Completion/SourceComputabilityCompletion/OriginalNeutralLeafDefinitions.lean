module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeaf
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original function payload's tag, without parsing or changing any raw
value. Lambda payloads have tag one. -/
def lambdaFunctionTest : Program 1 :=
  same (leftOf (functionPayload (.projection 0))) (InternalLessThan.constantOne 1)

/-- Original tag-two application whose actual raw function is not a lambda.
The zero/successor branch is on the exact Boolean equality test above. -/
def neutralTest : Program 1 :=
  InternalAcceptance.conjunction
    (same (constructorTag (.projection 0)) (two 1))
    (InternalAcceptance.branch lambdaFunctionTest
      (InternalLessThan.constantOne 1) (InternalAcceptance.constantZero 1))

def neutralAt : Program 4 :=
  .composition neutralTest (fun _ : Fin 1 => .projection 0)

/-- Read the original Context coordinate of the unchanged paired parameter. -/
def windowAt (window : Program 1) : Program 4 :=
  .composition window (fun _ : Fin 1 => leftOf (.projection 3))

/-- Test the actual original edgeCode and separate parameter; there is no
replacement certificate or independently selected endpoint. -/
def guardAt (endpoint : Program 6) : Program 4 :=
  .composition (InternalParameterizedApplicationStepChecker.guardP endpoint)
    ![InternalParameterizedApplicationStepChecker.edgeStateP,.projection 3]

def trigger (endpoint : Program 6) (window : Program 1) : Program 4 :=
  InternalAcceptance.conjunction (windowAt window)
    (InternalAcceptance.conjunction neutralAt
      (same (guardAt endpoint) (InternalAcceptance.constantZero 4)))

def leafGuard (endpoint : Program 6) (window : Program 1) : Program 4 :=
  InternalAcceptance.branch (trigger endpoint window) (InternalLessThan.constantOne 4)
    (same (.projection 1) OriginalConstructorLeaf.expectedBottom)

/-- Retain the whole old leaf as a factor. Native all-input equality must pay
redundancy of the new guard, including malformed and rejected inputs. -/
def refined (endpoint : Program 6) (window : Program 1) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.conjunction oldStep (leafGuard endpoint window)

def endpoint (p : GlobalSourcePackage.Inputs) : Program 6 :=
  InternalParameterizedStructuralEndpointGuard.selectedEndpoint
    (OuterSelection.data p.base p.window)

/-- One original tuple is changed before any window or Gamma is selected. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined (endpoint p) p.window p.oldStep }

/-- Internal raw-root law at the SAME original state, endpoint and leaf.
Window, neutral tag, original zero guard and type are arithmetic graph
premises. The conclusion is the literal original same-type bottom code. -/
def NeutralBottom (endpoint : Program 6) (window : Program 1) (leaf : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target certificate parameter state typeCode : OTerm alpha),
  Nonempty (Derivation body Delta
    ((OriginalConstructorLeaf.accepted leaf source target certificate parameter ⊓
      (graph3 edgeCode state source target certificate ⊓
        (graph2 (BottomRepresentative.windowAt window) InternalOriginalStepGuard.one
            source parameter ⊓
          (graph1 neutralTest InternalOriginalStepGuard.one source ⊓
            (graph2 (InternalParameterizedApplicationStepChecker.guardP endpoint)
                OrdinaryArithmetic.zeroTerm state parameter ⊓
              graph1 InternalUnpair.left typeCode source))))).imp
      (graph1 BottomRepresentative.bottomCode target typeCode)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeaf
