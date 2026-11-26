module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.DeletionChainProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceSyntax
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (emb suc sucRelabel)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst numeralSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open InternalQuotientComparisonSyntaxProof (orderSubst)
open CodedDeletionTraceDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fieldsSubst {beta : Type} (entry left right parameter gamma : OTerm alpha) (ts : alpha → OTerm beta) :
 (StateFields entry left right parameter gamma).subst (fun a => emb (ts a)) = StateFields (entry.subst ts) (left.subst ts) (right.subst ts) (parameter.subst ts) (gamma.subst ts) := by
 simp only [StateFields,conjunctionSubst,graph1,graph2,graph3,programSubst,consTermSubst,emptySubst,
   OriginalContextInsertionSyntaxProof.lengthSubst,OriginalContextInsertion.Below,orderSubst]
theorem metadataSubst {beta : Type} (entry count cutoff selectedType : OTerm alpha) (ts : alpha → OTerm beta) :
 (Metadata entry count cutoff selectedType).subst (fun a => emb (ts a)) = Metadata (entry.subst ts) (count.subst ts) (cutoff.subst ts) (selectedType.subst ts) := by
 simp only [Metadata,conjunctionSubst,graph1,graph2,graph3,programSubst,consTermSubst,emptySubst,
   OriginalContextInsertionSyntaxProof.lengthSubst,OriginalContextInsertion.Below,orderSubst]
theorem transitionSubst {beta : Type} (left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType : OTerm alpha) (ts : alpha → OTerm beta) :
 (DeletionChainDefinitions.Transition left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType).subst (fun a => emb (ts a)) = DeletionChainDefinitions.Transition (left.subst ts) (right.subst ts) (nextLeft.subst ts) (nextRight.subst ts) (parameter.subst ts) (nextParameter.subst ts) (c.subst ts) (gamma.subst ts) (nextGamma.subst ts) (count.subst ts) (cutoff.subst ts) (selectedType.subst ts) := by
 simp only [DeletionChainDefinitions.Transition,conjunctionSubst,graph1,graph2,graph3,programSubst,consTermSubst,emptySubst,
   OriginalContextInsertionSyntaxProof.lengthSubst,OriginalContextInsertion.Below,orderSubst]
theorem stateSubst {beta : Type} (trace index left right parameter gamma : OTerm alpha) (ts : alpha → OTerm beta) :
 (StateAt trace index left right parameter gamma).subst (fun a => emb (ts a)) = StateAt (trace.subst ts) (index.subst ts) (left.subst ts) (right.subst ts) (parameter.subst ts) (gamma.subst ts) := by
 unfold StateAt
 rw [existsSubst,liftedEmbedding]
 unfold stateMatrix
 simp only [conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,fieldsSubst,metadataSubst,
   transitionSubst,liftSubst,Term.subst,Sum.elim_inr,InternalTagArithmeticSyntaxProof.sucSubst]
theorem stepSubst {beta : Type} (trace index c : OTerm alpha) (ts : alpha → OTerm beta) :
 (StepAt trace index c).subst (fun a => emb (ts a)) = StepAt (trace.subst ts) (index.subst ts) (c.subst ts) := by
 unfold StepAt
 rw [OriginalContextInsertionSyntaxProof.blockSubst,liftedEmbedding]
 unfold stepMatrix
 simp only [conjunctionSubst,graph2,programSubst,consTermSubst,emptySubst,fieldsSubst,metadataSubst,
   transitionSubst,liftSubst,Term.subst,Sum.elim_inr,InternalTagArithmeticSyntaxProof.sucSubst]
theorem allSubst {beta : Type} (trace steps c : OTerm alpha) (ts : alpha → OTerm beta) :
 (AllSteps trace steps c).subst (fun a => emb (ts a)) = AllSteps (trace.subst ts) (steps.subst ts) (c.subst ts) := by
 unfold AllSteps stepsBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [OriginalContextInsertion.Below,orderSubst,stepSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem fieldsRename {beta : Type} (entry left right parameter gamma : OTerm alpha) (j : alpha → beta) :
 (StateFields entry left right parameter gamma).relabel j = StateFields (entry.relabel j) (left.relabel j) (right.relabel j) (parameter.relabel j) (gamma.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (StateFields entry left right parameter gamma).subst (fun a => emb (.var (j a))) = _
 rw [fieldsSubst]
 simp only [← termRelabelAsSubst]
theorem metadataRename {beta : Type} (entry count cutoff selectedType : OTerm alpha) (j : alpha → beta) :
 (Metadata entry count cutoff selectedType).relabel j = Metadata (entry.relabel j) (count.relabel j) (cutoff.relabel j) (selectedType.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Metadata entry count cutoff selectedType).subst (fun a => emb (.var (j a))) = _
 rw [metadataSubst]
 simp only [← termRelabelAsSubst]
theorem transitionRename {beta : Type} (left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType : OTerm alpha) (j : alpha → beta) :
 (DeletionChainDefinitions.Transition left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType).relabel j = DeletionChainDefinitions.Transition (left.relabel j) (right.relabel j) (nextLeft.relabel j) (nextRight.relabel j) (parameter.relabel j) (nextParameter.relabel j) (c.relabel j) (gamma.relabel j) (nextGamma.relabel j) (count.relabel j) (cutoff.relabel j) (selectedType.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (DeletionChainDefinitions.Transition left right nextLeft nextRight parameter nextParameter c gamma nextGamma count cutoff selectedType).subst (fun a => emb (.var (j a))) = _
 rw [transitionSubst]
 simp only [← termRelabelAsSubst]
theorem stateRename {beta : Type} (trace index left right parameter gamma : OTerm alpha) (j : alpha → beta) :
 (StateAt trace index left right parameter gamma).relabel j = StateAt (trace.relabel j) (index.relabel j) (left.relabel j) (right.relabel j) (parameter.relabel j) (gamma.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (StateAt trace index left right parameter gamma).subst (fun a => emb (.var (j a))) = _
 rw [stateSubst]
 simp only [← termRelabelAsSubst]
theorem stepRename {beta : Type} (trace index c : OTerm alpha) (j : alpha → beta) :
 (StepAt trace index c).relabel j = StepAt (trace.relabel j) (index.relabel j) (c.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (StepAt trace index c).subst (fun a => emb (.var (j a))) = _
 rw [stepSubst]
 simp only [← termRelabelAsSubst]
theorem allRename {beta : Type} (trace steps c : OTerm alpha) (j : alpha → beta) :
 (AllSteps trace steps c).relabel j = AllSteps (trace.relabel j) (steps.relabel j) (c.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (AllSteps trace steps c).subst (fun a => emb (.var (j a))) = _
 rw [allSubst]
 simp only [← termRelabelAsSubst]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceSyntax
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.CodedDeletionTraceSyntax
