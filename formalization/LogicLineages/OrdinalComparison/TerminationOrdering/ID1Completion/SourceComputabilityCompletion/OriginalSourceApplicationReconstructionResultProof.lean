module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionResultProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationStepPeel (graph5)
open InternalApplicationCertificateConstructors InternalApplicationStepPeelSupportProof
open InternalAcceptanceBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open NumberedLeastCodeRepresentative (typeNumber)
open InternalTagArithmeticSyntaxProof (z)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The original graph-level window and arrow witnesses activate both
original Object branches. Their actual output is accepted by the unchanged
application checker without any native evaluation premise. -/
theorem acceptedAt (oldComp : JointGammaComputability.Data) (data : Data) (window : Program 1)
    (oldVertex oldResult : Program 5) (context : Nat) (sigma tau : Ty)
    (functionObject argumentObject vertexObject : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (graph1 window InternalOriginalStepGuard.one (numeral context))))
    (har : Nonempty (Derivation body Gamma
      (graph2 InternalListCodec.consCode (numeral (typeNumber (.arrow sigma tau)))
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)))))
    (hd : Nonempty (Derivation body Gamma
      (InternalComputabilityDownward.domain
        (Outer.computability oldComp data window oldVertex oldResult) context sigma tau
        functionObject argumentObject)))
    (hr : Nonempty (Derivation body Gamma
      (graph5 (Outer.resultBranch (Path.vertex data window oldVertex)) vertexObject (numeral context)
        (numeral (typeNumber sigma)) (numeral (typeNumber tau)) functionObject argumentObject))) :
    Nonempty (Derivation body Gamma
      (InternalComputabilityApplication.accepted
        (Outer.computability oldComp data window oldVertex oldResult) sigma tau (numeral context)
        functionObject argumentObject vertexObject)) := by
  let xs : Fin 5 → OTerm alpha := Fin.cons (numeral context)
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons functionObject (Fin.cons argumentObject Fin.elim0))))
  have hactive := ApplicationGuardedActivationProof.activationAt window
    (Outer.baseComputability oldComp data window).typed (Outer.baseComputability oldComp data window).guard
    Outer.arrow (numeral context) (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (numeral (typeNumber (.arrow sigma tau))) functionObject argumentObject
    hw har (andLeft (andLeft hd)) (andRight (andLeft hd)) (andRight hd)
  have hresult := successorBranchIntro (Outer.resultActivation oldComp data window) oldResult
    (Outer.resultBranch (Path.vertex data window oldVertex)) vertexObject z xs hactive hr
  exact InternalApplicationGraphProof.activeAccept (Outer.resultActivation oldComp data window)
    (Outer.result oldComp data window oldVertex oldResult) oldComp.application xs vertexObject hactive hresult

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionResultProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceApplicationReconstructionResultProof
