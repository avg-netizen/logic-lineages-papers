module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherTransferProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineGenericProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherPipelineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
abbrev observers := ObservedOtherPipelineGenericProof.observers
theorem priorValueAtMarks (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output parameter : OTerm alpha) (marks : Fin 6 → OTerm alpha)
 (hd : Nonempty (Derivation body Delta (Domain p H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2 (minimumInputs p H G W P).base.oldRepresentative output input parameter)))
 (hother : Nonempty (Derivation body Delta (graph1 OriginalLambdaTraversalInternal.otherTag (suc z) input)))
 (hmarks : ∀ i, Nonempty (Derivation body Delta (graph1 (observers i) (marks i) input))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeaf.priorData (minimumInputs p H G W P) H G W).oldRepresentative output input parameter)) := by
 let m := minimumInputs p H G W P
 let raw := OriginalRankGuardedLeafTupleProof.rawData m H G W
 let window := (OriginalRankGuardedLeaf.refined m H G W).window
 have hactive : Nonempty (Derivation body Delta (graph2 (OriginalFunctionNeutrality.active raw window) (suc z) input parameter)) :=
   EvaluatorKeyOtherDomainProof.conditionFromDomain p H G W P input parameter hd
 have hh := EvaluatorKeyOtherMinimumProof.minimumHit p H G W P input output parameter hd hm
 have ha := EvaluatorKeyOtherDomainProof.admitted p H G W input output parameter hd (andLeft hh) (andRight hh)
 have hot := EvaluatorKeyOtherTransferProof.otherTransfer (baseRepresentative p H G W) H G (member p H G W) W input output parameter ha hother
 have hraw := EvaluatorKeyOtherGuardProof.initialValue p H G W P input output parameter (marks 0) hd hm (hmarks 0)
 exact ObservedOtherPipelineGenericProof.pipeline raw window input output parameter marks hactive hraw hmarks
   (fun i => SixSol20261113.Erasure.EvaluatorOtherMarksProof.actualOtherMarks
     (baseRepresentative p H G W) H G (member p H G W) W body alpha Delta input output parameter (marks i) ha hother hot)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherPipelineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyOtherPipelineProof
