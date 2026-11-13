module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPipelineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPriorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- The real pre-sidecar representative returns the actual observed minimum;
all six mark queries and all guard acceptances are discharged internally. -/
theorem priorValue (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (input output parameter : OTerm alpha)
 (hd : Nonempty (Derivation body Delta (OriginalActiveClassKernel.Domain
   (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W input parameter)))
 (hm : Nonempty (Derivation body Delta (graph2
   (OriginalClassContextAllPositionSelection.inputs (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P).base.oldRepresentative output input parameter))) :
 Nonempty (Derivation body Delta (graph2
   (OriginalRankGuardedLeaf.priorData (OriginalClassContextAllPositionSelection.inputs
     (OriginalStructuralClassKeyDefinitions.inputs p H G W) H G W P) H G W).oldRepresentative output input parameter)) := by
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases
   ObservedOtherPipelineProof.observers (Fin.cons input Fin.elim0) _
 intro beta j Theta values hj hg
 have hd' := renameInto hd j Theta hj
 have hm' := renameInto hm j Theta hj
 rw [OriginalActiveKernelMinimumSupportProof.domainRename] at hd'
 rw [graph2Rename] at hm' ⊢
 have hv : ∀ i, Nonempty (Derivation body Theta
     (graph1 (ObservedOtherPipelineProof.observers i) (values i) (input.relabel j))) := by
   intro i
   simpa only [consTermRename,InternalControlGraphSupportProof.emptyRename] using hg i
 exact ObservedOtherPipelineProof.priorValueAtMarks p H G W P
   (input.relabel j) (output.relabel j) (parameter.relabel j) values hd' hm' hv
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPriorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedOtherPriorProof
