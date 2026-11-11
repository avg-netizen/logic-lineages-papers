module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstruction
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Retain the original Object inputs and the supplied actual target-function
typing/application graphs. Both new Objects are literal original pairs at
the SAME runtime Gamma. Their application uses the SAME requested argument
Object; its raw argument normalization remains inside the original actualJ.
The target function need not remain non-lambda. -/
def Recovered {alpha : Type} (data : Data) (window : Program 1)
    (comp : JointGammaComputability.Data) (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex targetFunctionObject vertexObject : OTerm alpha) : Formula alpha :=
  OriginalSourceNeutralApplication.Recovered data window comp context sigma tau
      functionObject argumentObject outputObject gammaCode function argument out parameter ⊓
    (InternalOriginalUniformApplicationTyping.typedGraph data targetFunction
        (numeral (typeNumber (.arrow sigma tau))) parameter ⊓
      (InternalParameterizedCanonicalResultFold.applicationGraph data vertex
          (numeral (typeNumber sigma)) (numeral (typeNumber tau)) targetFunction argument parameter ⊓
        (graph2 InternalPairing.pairing targetFunctionObject gammaCode targetFunction ⊓
          (graph2 InternalPairing.pairing vertexObject gammaCode vertex ⊓
            (InternalComputabilityApplication.typed comp (.arrow sigma tau)
                (numeral context) targetFunctionObject ⊓
              (InternalComputabilityDownward.domain comp context sigma tau
                  targetFunctionObject argumentObject ⊓
                (InternalComputabilityApplication.accepted comp sigma tau (numeral context)
                    targetFunctionObject argumentObject vertexObject ⊓
                  InternalComputabilityApplication.typed comp tau (numeral context) vertexObject)))))))

/-- The existing exposed Object inputs and the two paid aligned target
graphs suffice to reconstruct the original accepted Object application.
Original pairing totality binds BOTH new Objects internally. No new runtime
coordinate, active-window, codomain-member, fold-fixedness, non-lambda or
source-certificate premise is supplied for the new target function. -/
def ApplicationReconstruction (data : Data) (window : Program 1)
    (comp : JointGammaComputability.Data) (context : Nat) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (sigma tau : Ty)
    (functionObject argumentObject outputObject gammaCode function argument out parameter
      targetFunction vertex : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation body Gamma
    (OriginalSourceNeutralApplication.Recovered data window comp context sigma tau
      functionObject argumentObject outputObject gammaCode function argument out parameter)) →
  Nonempty (Derivation body Gamma
    (InternalOriginalUniformApplicationTyping.typedGraph data targetFunction
      (numeral (typeNumber (.arrow sigma tau))) parameter)) →
  Nonempty (Derivation body Gamma
    (InternalParameterizedCanonicalResultFold.applicationGraph data vertex
      (numeral (typeNumber sigma)) (numeral (typeNumber tau)) targetFunction argument parameter)) →
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ targetFunctionObject vertexObject : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered data window comp context sigma tau
        (functionObject.relabel j) (argumentObject.relabel j) (outputObject.relabel j)
        (gammaCode.relabel j) (function.relabel j) (argument.relabel j)
        (out.relabel j) (parameter.relabel j) (targetFunction.relabel j) (vertex.relabel j)
        targetFunctionObject vertexObject)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstruction
