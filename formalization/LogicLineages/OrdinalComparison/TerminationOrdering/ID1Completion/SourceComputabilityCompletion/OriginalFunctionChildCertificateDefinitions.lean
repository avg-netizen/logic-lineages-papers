module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificate
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain the entire accepted original Object application at the first
vertex, its SAME child quotient edge and its original child certificate.
The new witness is literally one original list entry: pair the target raw
function with that child certificate, then cons it onto the original nil
code. Its conclusion is the ORIGINAL source H+ certificate from the supplied
function Object to the already reconstructed target-function Object.
The runtime Gamma, parameter and requested argument Object are unchanged. -/
def Recovered {alpha : Type} (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data)
    (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject child entry pathCode : OTerm alpha) :
    Formula alpha :=
  OriginalSourceApplicationReconstruction.Recovered data window comp context sigma tau
      functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject ⊓
    (edgeAccepted data oldStep function targetFunction child parameter ⊓
      (graph2 InternalPairing.pairing entry targetFunction child ⊓
        (graph2 InternalListCodec.consCode pathCode entry OrdinaryArithmetic.zeroTerm ⊓
          InternalAccessibilityRules.certificate src false context
            functionObject targetFunctionObject pathCode)))

/-- Only the already accepted original Object reconstruction and its SAME
function-child quotient edge are caller premises. Bind both new code values
internally and derive the ORIGINAL source certificate, including both
literal positive guards, Object typing and SAME-Gamma checks. There is no
non-lambda restriction on the reduct, no supplied spine/mark assumption,
and no conversion of native calibration into an arithmetic derivation. -/
def FunctionChildCertificates (data : Data) (window : Program 1) (oldStep : Program 4)
    (src : SourcePresentation.Data) (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (alpha : Type) (Gamma : List (Formula alpha)) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject child : OTerm alpha)
    (psi : Formula alpha),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (OriginalSourceApplicationReconstruction.Recovered data window comp context sigma tau
      functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject)) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma
    (edgeAccepted data oldStep function targetFunction child parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ entry pathCode : OTerm beta,
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta
      (Recovered data window oldStep src comp context sigma tau
        (functionObject.relabel j) (argumentObject.relabel j) (outputObject.relabel j)
        (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
        (out.relabel j) (parameter.relabel j) (targetFunction.relabel j) (vertex.relabel j)
        (targetFunctionObject.relabel j) (vertexObject.relabel j) (child.relabel j)
        entry pathCode)) →
    Nonempty (Derivation (SourcePresentation.sourceBody src context) Delta (psi.relabel j))) →
  Nonempty (Derivation (SourcePresentation.sourceBody src context) Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificate
