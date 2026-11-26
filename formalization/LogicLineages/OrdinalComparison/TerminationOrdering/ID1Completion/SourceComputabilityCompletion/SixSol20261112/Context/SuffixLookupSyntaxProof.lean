module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationValidityStackAppendSyntaxProof (graph2Subst)
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc emb varBind nextTerm bindTerm bindEmbedding nextEmbedding)
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalAdditionLawsProof (add addSubst impSubst)
open InternalOriginalOrderSyntaxProof (addRelabel)
open OriginalContextInsertion (lengthGraph)
open OriginalContextInsertionSyntaxProof (lengthSubst lengthRename)
open OriginalTypedDecoderTransportLogicalProof (iffRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph InternalRawListRecursion.lookup
  InternalApplicationValidityStackAppend.append OriginalContextInsertion.length

def result (count front suffix joined cutoff value : OTerm alpha) : Formula alpha :=
  (graph2 InternalRawListRecursion.lookup value (add count cutoff) joined).iff
    (graph2 InternalRawListRecursion.lookup value cutoff suffix)

def fields (count front suffix joined : OTerm alpha) : Formula alpha :=
  lengthGraph count front ⊓ graph2 InternalApplicationValidityStackAppend.append joined front suffix

def rowBody (count : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
    (result (count.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1))
      (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))

def row (count : OTerm alpha) : Formula alpha := allBlock (rowBody count)

theorem iffSubst {beta : Type} (P Q : Formula alpha) (ts : alpha → Term beta) :
    (P.iff Q).subst ts = (P.subst ts).iff (Q.subst ts) := rfl

theorem resultSubst {beta : Type} (count front suffix joined cutoff value : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (result count front suffix joined cutoff value).subst (fun a => emb (ts a)) =
      result (count.subst ts) (front.subst ts) (suffix.subst ts)
        (joined.subst ts) (cutoff.subst ts) (value.subst ts) := by
  simp only [result,iffSubst,graph2Subst,addSubst]

theorem resultRename {beta : Type} (count front suffix joined cutoff value : OTerm alpha)
    (j : alpha → beta) :
    (result count front suffix joined cutoff value).relabel j =
      result (count.relabel j) (front.relabel j) (suffix.relabel j)
        (joined.relabel j) (cutoff.relabel j) (value.relabel j) := by
  simp only [result,iffRename,graph2Rename,addRelabel]

theorem fieldsSubst {beta : Type} (count front suffix joined : OTerm alpha)
    (ts : alpha → OTerm beta) :
    (fields count front suffix joined).subst (fun a => emb (ts a)) =
      fields (count.subst ts) (front.subst ts) (suffix.subst ts) (joined.subst ts) := by
  simp only [fields,conjunctionSubst,lengthSubst,graph2Subst]

theorem fieldsRename {beta : Type} (count front suffix joined : OTerm alpha)
    (j : alpha → beta) :
    (fields count front suffix joined).relabel j =
      fields (count.relabel j) (front.relabel j) (suffix.relabel j) (joined.relabel j) := by
  simp only [fields,conjunctionRename,lengthRename,graph2Rename]

theorem rowSubst {beta : Type} (count : OTerm alpha) (ts : alpha → OTerm beta) :
    (row count).subst (fun a => emb (ts a)) = row (count.subst ts) := by
  unfold row rowBody
  rw [allBlockSubst,liftedEmbedding,impSubst]
  simp only [fieldsSubst,resultSubst,liftSubst,Term.subst,Sum.elim_inr]

theorem rowRename {beta : Type} (count : OTerm alpha) (j : alpha → beta) :
    (row count).relabel j = row (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (row count).subst (fun a => emb (.var (j a))) = _
  rw [rowSubst]
  simp only [← termRelabelAsSubst]

theorem rowWitness (count front suffix joined cutoff value : OTerm alpha) :
    (rowBody count).subst
      (Sum.elim Term.var (fun i => emb (![front,suffix,joined,cutoff,value] i))) =
      (fields count front suffix joined).imp (result count front suffix joined cutoff value) := by
  have he : (Sum.elim Term.var (fun i => emb (![front,suffix,joined,cutoff,value] i))) =
      (fun x => emb (Sum.elim Term.var ![front,suffix,joined,cutoff,value] x)) := by
    funext x
    cases x <;> rfl
  unfold rowBody
  rw [he,impSubst]
  simp only [fieldsSubst,resultSubst,witnessLift,Term.subst,Sum.elim_inr]
  rfl

theorem rowInstantiate (count : OTerm (alpha ⊕ Fin 1)) (t : OTerm alpha) :
    instantiate (row count) (emb t) = row (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,rowSubst]

theorem rowSuccessor (count : OTerm (alpha ⊕ Fin 1)) :
    successorInstance (row count) = row (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,rowSubst]

theorem rowApply (count front suffix joined cutoff value : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (row count)))
    (hf : Nonempty (Derivation body Delta (fields count front suffix joined))) :
    Nonempty (Derivation body Delta (result count front suffix joined cutoff value)) := by
  have h := actualFiniteUniversalElimination body alpha 5 Delta (rowBody count)
    (fun i => emb (![front,suffix,joined,cutoff,value] i)) hi
  rw [rowWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hf⟩ := hf
  exact ⟨Derivation.implicationElimination h hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.SuffixLookupSyntaxProof
