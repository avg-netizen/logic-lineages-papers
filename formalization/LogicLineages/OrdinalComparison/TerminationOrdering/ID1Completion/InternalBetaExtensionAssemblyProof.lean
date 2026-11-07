module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalRelationalCRT InternalRelationalCRTSyntaxProof InternalRelationalCRTChoiceProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalLeastNumberSyntaxProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalDerivationRenamingSyntaxProof InternalBetaTotalitySyntaxProof InternalBetaDivisionSyntaxProof
open InternalBetaTotality InternalBetaTotalityProof InternalBetaUniquenessProof
open InternalBetaCoding InternalBetaCodingSyntaxProof InternalBetaExtension InternalBetaExtensionSyntaxProof
open InternalQuotientComparisonProof InternalQuotientComparisonSyntaxProof InternalBezoutExistenceConsumerProof
open InternalBetaExtensionSupportProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem betaTransfer (a b c d i s r : OTerm α)
    (hs : Derivation body Gamma (beta a b i s))
    (hn : Derivation body Gamma (beta c d i s))
    (hr : Derivation body Gamma (beta a b i r)) :
    Nonempty (Derivation body Gamma (beta c d i r)) := by
  obtain ⟨hu⟩ := actualOriginalBetaUniqueness body α a b i s r
  rw [onEquality] at hu
  have he := Derivation.implicationElimination (weakenClosed hu Gamma)
    (Derivation.conjunctionIntroduction hs hr)
  exact ⟨betaOutputTransport c d i s r he hn⟩

theorem sameAtCommon (a b c d i s : OTerm α)
    (ho : Nonempty (Derivation body Gamma (beta a b i s)))
    (hn : Nonempty (Derivation body Gamma (beta c d i s))) :
    Nonempty (Derivation body Gamma (sameAt a b c d i)) := by
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 1)
  let B := b.relabel (Sum.inl : α → α ⊕ Fin 1)
  let C := c.relabel (Sum.inl : α → α ⊕ Fin 1)
  let D := d.relabel (Sum.inl : α → α ⊕ Fin 1)
  let I := i.relabel (Sum.inl : α → α ⊕ Fin 1)
  let S := s.relabel (Sum.inl : α → α ⊕ Fin 1)
  let r : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let Delta := Gamma.map weaken
  have hj : ∀ f ∈ Gamma, f.relabel Sum.inl ∈ Delta := by
    intro f hf; exact List.mem_map.mpr ⟨f,hf,rfl⟩
  obtain ⟨ho⟩ := renameInto ho Sum.inl Delta hj
  obtain ⟨hn⟩ := renameInto hn Sum.inl Delta hj
  rw [beta,betaRename] at ho hn
  have forward : Nonempty (Derivation body Delta ((beta A B I r).imp (beta C D I r))) := by
    obtain ⟨h⟩ := betaTransfer A B C D I S r (addHyp ho _) (addHyp hn _)
      (Derivation.hypothesis List.mem_cons_self)
    exact ⟨Derivation.implicationIntroduction h⟩
  have reverse : Nonempty (Derivation body Delta ((beta C D I r).imp (beta A B I r))) := by
    obtain ⟨h⟩ := betaTransfer C D A B I S r (addHyp hn _) (addHyp ho _)
      (Derivation.hypothesis List.mem_cons_self)
    exact ⟨Derivation.implicationIntroduction h⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨reverse⟩ := reverse
  exact ⟨Derivation.universalIntroduction (Derivation.conjunctionIntroduction forward reverse)⟩

/-- Open the chosen relation witness and retain its literal new beta graph. -/
theorem appendChoiceCases (a b n z c d i : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (existsOne (residueRelation a b n z i ⊓
      beta (c.relabel Sum.inl) (d.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))))))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (r : OTerm β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (point (a.relabel j) (b.relabel j) (n.relabel j)
        (z.relabel j) (i.relabel j) r)) →
      Nonempty (Derivation body Delta (beta (c.relabel j) (d.relabel j) (i.relabel j) r)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply existsCases Gamma _ psi h
  intro β j Delta r hj hr
  rw [infRename,residueRelationRename,beta,betaRename,infInstantiate,
    residueRelationInstantiate,betaInstantiate] at hr
  simp only [Term.relabel_relabel,mapInl,varMap,liftBind,varBind] at hr
  have ht (t : OTerm α) : (t.relabel (Sum.inl ∘ j)).subst (bindTerm r) = t.relabel j := by
    rw [← Term.relabel_relabel,liftBind]
  simp only [ht] at hr
  obtain ⟨hr⟩ := hr
  exact k β j Delta r hj ⟨Derivation.conjunctionLeft hr⟩ ⟨Derivation.conjunctionRight hr⟩

theorem codedPrefix (a b n z c d i : OTerm α)
    (h : Derivation body Gamma (codedBelow (appendRelation a b n z) c d (suc n)))
    (hi : Derivation body Gamma (ltF i n)) :
    Nonempty (Derivation body Gamma (sameAt a b c d i)) := by
  obtain ⟨hn⟩ := selfLtSucc (body := body) (Gamma := Gamma) n
  obtain ⟨ht⟩ := actualOriginalOrderTransitivity body α i n (suc n)
  have hi' := Derivation.implicationElimination (weakenClosed ht Gamma)
    (Derivation.conjunctionIntroduction hi hn)
  have hc := codedAtAppend a b n z c d i h hi'
  apply appendChoiceCases a b n z c d i (sameAt a b c d i) hc
  intro β j Delta r hj hp hb
  obtain ⟨hp⟩ := hp
  obtain ⟨hi⟩ := renameInto ⟨hi⟩ j Delta hj
  rw [orderRename] at hi
  have ho := pointPrefix _ _ _ _ _ r hi hp
  rw [sameAtRename]
  exact sameAtCommon _ _ _ _ _ r ho hb

theorem codedSameBelow (a b n z c d : OTerm α)
    (h : Nonempty (Derivation body Gamma (codedBelow (appendRelation a b n z) c d (suc n)))) :
    Nonempty (Derivation body Gamma (sameBelow a b c d n)) := by
  let x : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let N := n.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := ltF x N :: Gamma.map weaken
  have hj : ∀ f ∈ Gamma, f.relabel Sum.inl ∈ Delta := by
    intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  obtain ⟨h⟩ := renameInto h Sum.inl Delta hj
  rw [codedBelowRename,appendRelationRename,sucRelabel] at h
  obtain ⟨hp⟩ := codedPrefix _ _ _ _ _ _ x h (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction hp)⟩

theorem codedLast (a b n z c d : OTerm α)
    (h : Derivation body Gamma (codedBelow (appendRelation a b n z) c d (suc n))) :
    Nonempty (Derivation body Gamma (beta c d n z)) := by
  obtain ⟨hn⟩ := selfLtSucc (body := body) (Gamma := Gamma) n
  have hc := codedAtAppend a b n z c d n h hn
  apply appendChoiceCases a b n z c d n (beta c d n z) hc
  intro β j Delta r hj hp hb
  obtain ⟨hp⟩ := hp
  obtain ⟨hb⟩ := hb
  obtain ⟨he⟩ := pointLast _ _ _ _ r hp
  rw [beta,betaRename]
  exact ⟨betaOutputTransport _ _ _ _ _ he hb⟩

theorem codedExtension (a b n z c d : OTerm α)
    (h : Nonempty (Derivation body Gamma (codedBelow (appendRelation a b n z) c d (suc n)))) :
    Nonempty (Derivation body Gamma (extension a b n z)) := by
  obtain ⟨hp⟩ := codedSameBelow a b n z c d h
  obtain ⟨h⟩ := h
  obtain ⟨hz⟩ := codedLast a b n z c d h
  exact extensionIntroduction a b n z c d ⟨Derivation.conjunctionIntroduction hp hz⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionAssemblyProof
