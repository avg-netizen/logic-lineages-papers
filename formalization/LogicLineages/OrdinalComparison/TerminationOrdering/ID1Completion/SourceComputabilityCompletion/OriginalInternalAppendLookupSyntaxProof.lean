module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAdditionLawsProof (add addSubst)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalInternalAppendLookup
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst)
theorem tailFieldsSubst {beta : Type} (frontCount suffix index value suffixIndex suffixCount : OTerm alpha) (ts : alpha → OTerm beta) :
 (tailFields frontCount suffix index value suffixIndex suffixCount).subst (fun a => emb (ts a)) =
 tailFields (frontCount.subst ts) (suffix.subst ts) (index.subst ts) (value.subst ts) (suffixIndex.subst ts) (suffixCount.subst ts) := by
 simp only [tailFields,conjunctionSubst,eqnSubst,addSubst,lengthSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem tailSubst {beta : Type} (frontCount suffix index value : OTerm alpha) (ts : alpha → OTerm beta) :
 (Tail frontCount suffix index value).subst (fun a => emb (ts a)) =
 Tail (frontCount.subst ts) (suffix.subst ts) (index.subst ts) (value.subst ts) := by
 unfold Tail tailMatrix
 rw [blockSubst,liftedEmbedding,tailFieldsSubst]
 simp only [liftSubst,Term.subst,Sum.elim_inr]
theorem tailRename {beta : Type} (frontCount suffix index value : OTerm alpha) (j : alpha → beta) :
 (Tail frontCount suffix index value).relabel j =
 Tail (frontCount.relabel j) (suffix.relabel j) (index.relabel j) (value.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Tail frontCount suffix index value).subst (fun a => emb (.var (j a))) = _
 rw [tailSubst]
 simp only [← termRelabelAsSubst]
theorem resultSubst {beta : Type} (frontCount front suffix index value : OTerm alpha) (ts : alpha → OTerm beta) :
 (Result frontCount front suffix index value).subst (fun a => emb (ts a)) =
 Result (frontCount.subst ts) (front.subst ts) (suffix.subst ts) (index.subst ts) (value.subst ts) := by
 simp only [Result,orSubst,conjunctionSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst,tailSubst]
theorem resultRename {beta : Type} (frontCount front suffix index value : OTerm alpha) (j : alpha → beta) :
 (Result frontCount front suffix index value).relabel j =
 Result (frontCount.relabel j) (front.relabel j) (suffix.relabel j) (index.relabel j) (value.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (Result frontCount front suffix index value).subst (fun a => emb (.var (j a))) = _
 rw [resultSubst]
 simp only [← termRelabelAsSubst]
theorem tailWitness (frontCount suffix index value suffixIndex suffixCount : OTerm alpha) :
 (tailMatrix frontCount suffix index value).subst (Sum.elim Term.var (fun i => emb (![suffixIndex,suffixCount] i))) =
 tailFields frontCount suffix index value suffixIndex suffixCount := by
 have he : (Sum.elim Term.var (fun i => emb (![suffixIndex,suffixCount] i))) =
   (fun a => emb (Sum.elim Term.var ![suffixIndex,suffixCount] a)) := by funext a; cases a <;> rfl
 unfold tailMatrix
 rw [he,tailFieldsSubst]
 simp only [witnessLift,Term.subst,Sum.elim_inr]
 rfl
def fields (frontCount front suffix joined count index value : OTerm alpha) : Formula alpha :=
 lengthGraph frontCount front ⊓ (graph2 InternalApplicationValidityStackAppend.append joined front suffix ⊓
 (lengthGraph count joined ⊓ (Below index count ⊓ graph2 InternalRawListRecursion.lookup value index joined)))
def rowBody (frontCount : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
 (fields (frontCount.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
 (Result (frontCount.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 4)) (.var (.inr 5)))
def row (frontCount : OTerm alpha) : Formula alpha := allBlock (rowBody frontCount)
theorem fieldsSubst {beta : Type} (frontCount front suffix joined count index value : OTerm alpha) (ts : alpha → OTerm beta) :
 (fields frontCount front suffix joined count index value).subst (fun a => emb (ts a)) =
 fields (frontCount.subst ts) (front.subst ts) (suffix.subst ts) (joined.subst ts) (count.subst ts) (index.subst ts) (value.subst ts) := by
 simp only [fields,conjunctionSubst,lengthSubst,Below,orderSubst,graph2,programSubst,consTermSubst,emptySubst]
theorem fieldsRename {beta : Type} (frontCount front suffix joined count index value : OTerm alpha) (j : alpha → beta) :
 (fields frontCount front suffix joined count index value).relabel j =
 fields (frontCount.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j) (count.relabel j) (index.relabel j) (value.relabel j) := by
 simp only [fields,conjunctionRename,lengthRename,Below,orderRename,graph2Rename]
theorem rowSubst {beta : Type} (frontCount : OTerm alpha) (ts : alpha → OTerm beta) :
 (row frontCount).subst (fun a => emb (ts a)) = row (frontCount.subst ts) := by
 unfold row rowBody
 rw [allBlockSubst,liftedEmbedding,impSubst]
 simp only [fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]
theorem rowRename {beta : Type} (frontCount : OTerm alpha) (j : alpha → beta) :
 (row frontCount).relabel j = row (frontCount.relabel j) := by
 rw [formulaRelabelAsSubst]
 change (row frontCount).subst (fun a => emb (.var (j a))) = _
 rw [rowSubst]
 simp only [← termRelabelAsSubst]
theorem rowBodyWitness (frontCount front suffix joined count index value : OTerm alpha) :
 (rowBody frontCount).subst (Sum.elim Term.var (fun i => emb (![front,suffix,joined,count,index,value] i))) = (fields frontCount front suffix joined count index value).imp (Result frontCount front suffix index value) := by
 have he : (Sum.elim Term.var (fun i => emb (![front,suffix,joined,count,index,value] i))) = (fun x => emb (Sum.elim Term.var ![front,suffix,joined,count,index,value] x)) := by
  funext x
  cases x <;> rfl
 unfold rowBody
 rw [he,impSubst]
 simp only [fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
 rfl
theorem rowInstantiate (frontCount : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
 instantiate (row frontCount) (emb t) = row (frontCount.subst (bindTerm t)) := by
 rw [instantiate,bindEmbedding,rowSubst]
theorem rowSuccessor (frontCount : OTerm (alpha ⊕ Fin 1)) :
 successorInstance (row frontCount) = row (frontCount.subst nextTerm) := by
 rw [successorInstance,nextEmbedding,rowSubst]
theorem rowApply (frontCount front suffix joined count index value : OTerm alpha)
 (hr : Nonempty (Derivation body Delta (row frontCount)))
 (hf : Nonempty (Derivation body Delta (fields frontCount front suffix joined count index value))) :
 Nonempty (Derivation body Delta (Result frontCount front suffix index value)) := by
 have h := actualFiniteUniversalElimination body alpha 6 Delta (rowBody frontCount) (fun i => emb (![front,suffix,joined,count,index,value] i)) hr
 rw [rowBodyWitness] at h
 obtain ⟨h⟩ := h
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination h hf⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupSyntaxProof
