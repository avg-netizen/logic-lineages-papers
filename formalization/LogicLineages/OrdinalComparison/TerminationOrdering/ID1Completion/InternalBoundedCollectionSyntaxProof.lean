module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRelationalCRTProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalRelationalCRTSupportProof InternalBoundedCollection
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalOriginalOrderSyntaxProof
open InternalDerivationRenamingSyntaxProof InternalQuotientComparisonSyntaxProof
open InternalOriginalOrderProof InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof

theorem boundedRelationRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (K : OTerm α) (j : α → β) :
    (boundedRelation R K).relabel (Sum.map (Sum.map j id) id) =
    boundedRelation (R.relabel (Sum.map (Sum.map j id) id)) (K.relabel j) := by
  unfold boundedRelation
  change R.relabel (Sum.map (Sum.map j id) id) ⊓
    (ltF (.var (.inr 0)) ((K.relabel Sum.inl).relabel Sum.inl)).relabel (Sum.map (Sum.map j id) id) = _
  rw [orderRename]
  simp only [Term.relabel_relabel,varMap]
  rfl

theorem boundedRelationSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (K : OTerm α) (ts : α → OTerm β) :
    (boundedRelation R K).subst (fun x => emb (liftTerms (liftTerms ts) x)) =
    boundedRelation (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (K.subst ts) := by
  change (R ⊓ ltF _ _).subst _ = _
  rw [infSubst,orderSubst]
  simp only [liftSubst]
  rfl

theorem boundBelowRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (K n : OTerm α) (j : α → β) :
    (boundBelow R K n).relabel j =
    boundBelow (R.relabel (Sum.map (Sum.map j id) id)) (K.relabel j) (n.relabel j) := by
  rw [boundBelow,availableBelowRename,boundedRelationRename]
  rfl

theorem boundBelowSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (K n : OTerm α) (ts : α → OTerm β) :
    (boundBelow R K n).subst (fun x => emb (ts x)) =
    boundBelow (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (K.subst ts) (n.subst ts) := by
  rw [boundBelow,availableBelowSubst,boundedRelationSubst]
  rfl

theorem collectionRename {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (j : α → β) :
    (collection R n).relabel j =
    collection (R.relabel (Sum.map (Sum.map j id) id)) (n.relabel j) := by
  rw [collection,existsRename,boundBelowRename,relationLiftRename]
  simp only [collection,Term.relabel_relabel,mapInl,varMap]

theorem collectionSubst {α β : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (ts : α → OTerm β) :
    (collection R n).subst (fun x => emb (ts x)) =
    collection (R.subst (fun x => emb (liftTerms (liftTerms ts) x))) (n.subst ts) := by
  rw [collection,existsSubst,liftEmbedding,boundBelowSubst,relationLiftSubst]
  simp only [liftSubst]
  rfl

theorem collectionInstantiate {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (n : OTerm α) :
    instantiate (collection (R.relabel (Sum.map (Sum.map Sum.inl id) id)) (.var (.inr 0))) (emb n) =
    collection R n := by
  rw [instantiate,bindEmbedding,collectionSubst,relationLiftBind,varBind]

theorem collectionMatrixInstantiate {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (K n : OTerm α) :
    instantiate (boundBelow (R.relabel (Sum.map (Sum.map Sum.inl id) id)) (.var (.inr 0))
      (n.relabel Sum.inl)) (emb K) = boundBelow R K n := by
  rw [instantiate,bindEmbedding,boundBelowSubst,relationLiftBind,varBind,liftBind]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem collectionIntroduction (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (K n : OTerm α)
    (h : Nonempty (Derivation body Gamma (boundBelow R K n))) :
    Nonempty (Derivation body Gamma (collection R n)) := by
  obtain ⟨h⟩ := h
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb K)
  rw [collectionMatrixInstantiate]
  exact h

theorem collectionCases (Gamma : List (Formula α)) (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1))
    (n : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (collection R n)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (K : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (boundBelow (R.relabel (Sum.map (Sum.map j id) id)) K (n.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  obtain ⟨hk⟩ := k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.existentialElimination h hk⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSyntaxProof
