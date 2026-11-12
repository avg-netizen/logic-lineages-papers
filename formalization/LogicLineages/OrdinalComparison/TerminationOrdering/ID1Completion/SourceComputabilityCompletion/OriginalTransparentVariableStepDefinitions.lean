module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveKernelMinimumDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStep
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal ORIGINAL empty-path/direct-bottom StepCertificate, whose
replacement is the original same-type packed bottom. Input is packed source. -/
def certificateCode : Program 1 :=
  pairOf (InternalFixedWindowVertexDispatch.constant 1 0)
    (pairOf (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => InternalUnpair.left))
      (pairOf (InternalFixedWindowVertexDispatch.constant 1 3) (InternalFixedWindowVertexDispatch.constant 1 0)))

/-- Only the exact chosen bottom certificate at an original variable source
is replaced. Every other old leaf output is retained, including noncanonical
certificates and malformed/nonvariable raw input branches. -/
def active : Program 4 :=
  InternalAcceptance.conjunction OriginalConstructorLeaf.variableAt
    (InternalApplicationStepPeel.same (.projection 2)
      (.composition certificateCode (fun _ : Fin 1 => .projection 0)))

/-- Source validity here is the SAME original globally supplied source
program. Its concrete internal refinement is a separate existing supplier. -/
def sourceAt (source : Program 2) : Program 4 :=
  .composition source ![.projection 0,.projection 3]

def acceptedValue (source : Program 2) : Program 4 :=
  InternalAcceptance.conjunction (sourceAt source)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom)

def refined (source : Program 2) (oldStep : Program 4) : Program 4 :=
  InternalAcceptance.branch active oldStep (acceptedValue source)

/-- Refine only oldStep before the same existing selection pipeline. Source,
target, representative, type membership, window and all codecs stay literal. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with oldStep := refined p.base.oldSource p.oldStep }

/-- All premises are original source validity and actual constructor graphs.
Acceptance of oldStep, native calibration and transformed certificate
acceptance are not supplied as internal assumptions. -/
def IntroductionLaw (source : Program 2) (oldStep : Program 4) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert typ parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 source InternalOriginalStepGuard.one s parameter ⊓
      (graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one s ⊓
        (graph1 InternalUnpair.left typ s ⊓
          (graph1 BottomRepresentative.bottomCode t typ ⊓ graph1 certificateCode cert s)))).imp
      (graph4 (refined source oldStep) InternalOriginalStepGuard.one s t cert parameter)))

/- This is the original raw step-leaf constructor supplier. It is not the
entire selected checker/path certificate, contextual erasure transformer,
internal substitution/I/C, or the closed accessibility theorem. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStep 
