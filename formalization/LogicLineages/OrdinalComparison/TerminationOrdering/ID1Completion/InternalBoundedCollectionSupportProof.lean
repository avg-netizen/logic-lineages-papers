module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus SourceComputabilityFormulaSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalRelationalCRTSupportProof InternalBoundedCollection InternalBoundedCollectionSyntaxProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalPositiveUnfoldingSupportProof InternalLeastNumberSyntaxProof InternalOriginalOrderSyntaxProof
open InternalOriginalOrderProof InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalAdditionLawsProof InternalDerivationRenamingSyntaxProof InternalQuotientComparisonSyntaxProof

def witness {α : Type} (Q : Formula (α ⊕ Fin 1)) (K : OTerm α) : Formula α :=
  existsOne (Q ⊓ ltF (.var (.inr 0)) (K.relabel Sum.inl))

theorem witnessRename {α β : Type} (Q : Formula (α ⊕ Fin 1)) (K : OTerm α) (j : α → β) :
    (witness Q K).relabel j = witness (Q.relabel (Sum.map j id)) (K.relabel j) := by
  unfold witness
  rw [existsRename]
  change existsOne (Q.relabel (Sum.map j id) ⊓
    (ltF (.var (.inr 0)) (K.relabel Sum.inl)).relabel (Sum.map j id)) = _
  rw [orderRename]
  simp only [Term.relabel_relabel,mapInl,varMap]

theorem witnessSubst {α β : Type} (Q : Formula (α ⊕ Fin 1)) (K : OTerm α) (ts : α → OTerm β) :
    (witness Q K).subst (fun x => emb (ts x)) =
    witness (Q.subst (fun x => emb (liftTerms ts x))) (K.subst ts) := by
  unfold witness
  rw [existsSubst,liftEmbedding,infSubst,orderSubst,liftSubst]
  rfl

theorem boundBelowAt {α : Type} (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (K i : OTerm α) :
    instantiate (witness R (K.relabel Sum.inl)) (emb i) = witness (atIndex R i) K := by
  rw [instantiate,bindEmbedding,witnessSubst,liftBind]
  rfl

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
theorem witnessIntroduction (Q : Formula (α ⊕ Fin 1)) (K r : OTerm α)
    (hQ : Nonempty (Derivation body Gamma (instantiate Q (emb r))))
    (hr : Nonempty (Derivation body Gamma (ltF r K))) :
    Nonempty (Derivation body Gamma (witness Q K)) := by
  obtain ⟨hQ⟩ := hQ
  obtain ⟨hr⟩ := hr
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb r)
  rw [infInstantiate,orderInstantiate,varBind,liftBind]
  exact Derivation.conjunctionIntroduction hQ hr

theorem ltTrans (s t u : OTerm α) (hs : Nonempty (Derivation body Gamma (ltF s t)))
    (ht : Nonempty (Derivation body Gamma (ltF t u))) :
    Nonempty (Derivation body Gamma (ltF s u)) := by
  obtain ⟨hs⟩ := hs
  obtain ⟨ht⟩ := ht
  obtain ⟨h⟩ := actualOriginalOrderTransitivity body α s t u
  exact ⟨Derivation.implicationElimination (weakenClosed h Gamma) (Derivation.conjunctionIntroduction hs ht)⟩

theorem witnessMono (Q : Formula (α ⊕ Fin 1)) (K H : OTerm α)
    (h : Nonempty (Derivation body Gamma (witness Q K)))
    (hlt : Nonempty (Derivation body Gamma (ltF K H))) :
    Nonempty (Derivation body Gamma (witness Q H)) := by
  apply existsCases Gamma (Q ⊓ ltF (.var (.inr 0)) (K.relabel Sum.inl)) (witness Q H) h
  intro β j Delta r hj hr
  change Nonempty (Derivation body Delta (instantiate ((Q.relabel (Sum.map j id)) ⊓
    (ltF (.var (.inr 0)) (K.relabel Sum.inl)).relabel (Sum.map j id)) (emb r))) at hr
  have he : (ltF (.var (.inr 0)) (K.relabel Sum.inl)).relabel (Sum.map j id) =
      ltF (.var (.inr 0)) ((K.relabel j).relabel Sum.inl) := by
    rw [orderRename]
    simp only [Term.relabel_relabel,mapInl,varMap]
  rw [infInstantiate,he,orderInstantiate,varBind,liftBind] at hr
  obtain ⟨hr⟩ := hr
  have hlt' := renameInto hlt j Delta hj
  rw [orderRename] at hlt'
  rw [witnessRename]
  exact witnessIntroduction _ _ r ⟨Derivation.conjunctionLeft hr⟩
    (ltTrans r (K.relabel j) (H.relabel j) ⟨Derivation.conjunctionRight hr⟩ hlt')

theorem boundBelowMono (R : Formula ((α ⊕ Fin 1) ⊕ Fin 1)) (K H n : OTerm α)
    (h : Nonempty (Derivation body Gamma (boundBelow R K n)))
    (hlt : Nonempty (Derivation body Gamma (ltF K H))) :
    Nonempty (Derivation body Gamma (boundBelow R H n)) := by
  apply boundedMap (witness R (K.relabel Sum.inl)) (witness R (H.relabel Sum.inl)) n h
  apply Nonempty.intro
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  let Delta := witness R (K.relabel Sum.inl) :: Gamma.map weaken
  have hlt' := renameInto hlt Sum.inl Delta
    (by intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  rw [orderRename] at hlt'
  exact (witnessMono (body := body) (Gamma := Delta) R (K.relabel Sum.inl) (H.relabel Sum.inl)
    ⟨Derivation.hypothesis List.mem_cons_self⟩ hlt').some

theorem leftLtSuccAdd (K r : OTerm α) :
    Nonempty (Derivation body Gamma (ltF K (suc (add K r)))) := by
  apply actualOriginalOrderIntroduction body α Gamma K (suc (add K r)) r
  rw [onEquality]
  exact ⟨addSucc K r⟩

theorem rightLtSuccAdd (K r : OTerm α) :
    Nonempty (Derivation body Gamma (ltF r (suc (add K r)))) := by
  apply actualOriginalOrderIntroduction body α Gamma r (suc (add K r)) K
  rw [onEquality]
  exact ⟨trans (addSucc r K) (congSuc (InternalAdditionCancellationProof.commutativity r K))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSupportProof
