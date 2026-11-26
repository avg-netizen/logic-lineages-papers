module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterResultSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionBranchProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Rebuild the original Object result branch at its actual raw vertex.
This is the constructive reverse of the accepted resultPair supplier. -/
theorem resultBranchValue (vertexProgram : Program 5) (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject vertexObject gammaCode function argument parameter vertex : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.left gammaCode functionObject)))
    (hf : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.right function functionObject)))
    (ha : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.right argument argumentObject)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing parameter (numeral context) gammaCode)))
    (hv : Nonempty (Derivation body Gamma
      (graph5 vertexProgram vertex parameter
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument function)))
    (hpair : Nonempty (Derivation body Gamma
      (graph2 InternalPairing.pairing vertexObject gammaCode vertex))) :
    Nonempty (Derivation body Gamma
      (graph5 (Outer.resultBranch vertexProgram) vertexObject (numeral context)
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) functionObject argumentObject)) := by
  let xs : Fin 5 → OTerm alpha := Fin.cons (numeral context)
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons functionObject (Fin.cons argumentObject Fin.elim0))))
  let vp : Program 5 := .composition vertexProgram
    (Fin.cons (Outer.parameter (.projection 0) (.projection 3))
      (Fin.cons (.projection 1) (Fin.cons (.projection 2)
        (Fin.cons (rightOf (.projection 4)) (Fin.cons (rightOf (.projection 3)) Fin.elim0)))))
  have hleft := unaryValue InternalUnpair.left (.projection (3 : Fin 5))
    gammaCode functionObject xs hg (projectionValue 3 xs)
  have hrightF := unaryValue InternalUnpair.right (.projection (3 : Fin 5))
    function functionObject xs hf (projectionValue 3 xs)
  have hrightA := unaryValue InternalUnpair.right (.projection (4 : Fin 5))
    argument argumentObject xs ha (projectionValue 4 xs)
  have hparameter := OuterCarrierSupportProof.parameterValue (.projection (0 : Fin 5)) (.projection 3)
    (numeral context) functionObject gammaCode parameter xs
    (projectionValue 0 xs) (projectionValue 3 xs) hg hp
  have hvertex : Nonempty (Derivation body Gamma (programGraph vp vertex xs)) := by
    apply compositionValue vertexProgram _ vertex xs
      (Fin.cons parameter (Fin.cons (numeral (typeNumber sigma))
        (Fin.cons (numeral (typeNumber tau)) (Fin.cons argument (Fin.cons function Fin.elim0))))) hv
    intro i
    exact Fin.cases hparameter (Fin.cases (projectionValue 1 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases hrightA (Fin.cases hrightF (fun j => Fin.elim0 j))))) i
  exact binaryValue InternalPairing.pairing (leftOf (.projection (3 : Fin 5))) vp
    vertexObject gammaCode vertex xs hpair hleft hvertex

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionBranchProof
