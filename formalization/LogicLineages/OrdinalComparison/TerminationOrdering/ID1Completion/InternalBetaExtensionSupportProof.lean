module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSupportProof
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
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def betaOutputTransport (a b i r s : OTerm α) (he : Derivation body Gamma (eqn r s))
    (hr : Derivation body Gamma (beta a b i r)) : Derivation body Gamma (beta a b i s) := by
  have h := Derivation.equalityElimination
    (beta (a.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0)))
    (emb r) (emb s) he
  simp only [beta,betaInstantiate,liftBind,varBind] at h
  exact h hr

theorem ltEqualContradiction (i n : OTerm α) (hl : Derivation body Gamma (ltF i n))
    (he : Derivation body Gamma (eqn i n)) : Nonempty (Derivation body Gamma ⊥) := by
  have h := Derivation.equalityElimination (ltF (.var (.inr 0)) (n.relabel Sum.inl))
    (emb i) (emb n) he
  simp only [orderInstantiate,varBind,liftBind] at h
  obtain ⟨hn⟩ := actualOriginalOrderIrreflexivity body α n
  exact ⟨Derivation.implicationElimination (weakenClosed hn Gamma) (h hl)⟩

theorem pointPrefix (a b n z i r : OTerm α)
    (hl : Derivation body Gamma (ltF i n)) (hp : Derivation body Gamma (point a b n z i r)) :
    Nonempty (Derivation body Gamma (beta a b i r)) := by
  have left : Derivation body Gamma ((ltF i n ⊓ beta a b i r).imp (beta a b i r)) :=
    Derivation.implicationIntroduction (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))
  have right : Nonempty (Derivation body Gamma ((eqn i n ⊓ eqn r z).imp (beta a b i r))) := by
    have he : Derivation body ((eqn i n ⊓ eqn r z) :: Gamma) (eqn i n) :=
      Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)
    obtain ⟨hf⟩ := ltEqualContradiction i n (addHyp hl _) he
    exact ⟨Derivation.implicationIntroduction (Derivation.explosion hf)⟩
  obtain ⟨right⟩ := right
  exact ⟨disjunctionElimination hp left right⟩

theorem pointLast (a b n z r : OTerm α) (hp : Derivation body Gamma (point a b n z n r)) :
    Nonempty (Derivation body Gamma (eqn r z)) := by
  obtain ⟨hn⟩ := actualOriginalOrderIrreflexivity body α n
  have left : Derivation body Gamma ((ltF n n ⊓ beta a b n r).imp (eqn r z)) :=
    Derivation.implicationIntroduction (Derivation.explosion (Derivation.implicationElimination
      (weakenClosed hn _) (Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self))))
  have right : Derivation body Gamma ((eqn n n ⊓ eqn r z).imp (eqn r z)) :=
    Derivation.implicationIntroduction (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))
  exact ⟨disjunctionElimination hp left right⟩

theorem prefixWitness (a b n z i : OTerm α) (hl : Derivation body Gamma (ltF i n)) :
    Nonempty (Derivation body Gamma (existsOne (residueRelation a b n z i))) := by
  obtain ⟨ht⟩ := actualBetaTotality body α a b i
  have hp := weakenClosed ht Gamma
  let p : Formula (α ⊕ Fin 1) := beta (a.relabel Sum.inl) (b.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))
  let Delta := p :: Gamma.map weaken
  have hi : ∀ f ∈ Gamma, f.relabel Sum.inl ∈ Delta := by
    intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  obtain ⟨hl'⟩ := renameInto ⟨hl⟩ Sum.inl Delta hi
  rw [orderRename] at hl'
  exact ⟨existsMap hp (orLeft (Derivation.conjunctionIntroduction hl'
    (Derivation.hypothesis List.mem_cons_self)))⟩

theorem appendAvailable (a b n z : OTerm α) :
    Nonempty (Derivation body Gamma (availableBelow (appendRelation a b n z) (suc n))) := by
  have hp : Nonempty (Derivation body Gamma (bounded (existsOne (appendRelation a b n z)) n)) := by
    apply Nonempty.intro
    apply Derivation.universalIntroduction
    apply Derivation.implicationIntroduction
    exact (prefixWitness (a.relabel Sum.inl) (b.relabel Sum.inl) (n.relabel Sum.inl)
      (z.relabel Sum.inl) (.var (.inr 0)) (Derivation.hypothesis List.mem_cons_self)).some
  have hn : Nonempty (Derivation body Gamma (instantiate (existsOne (appendRelation a b n z)) (emb n))) := by
    rw [availableAtAppend]
    apply Nonempty.intro
    apply Derivation.existentialIntroduction (emb z)
    rw [residueRelationInstantiate]
    exact orRight (Derivation.conjunctionIntroduction (refl n) (refl z))
  exact boundedStep (existsOne (appendRelation a b n z)) n hp hn

/-- Every bounded code choice can be opened without disturbing the original parameters. -/
theorem codedAtAppend (a b n z c d i : OTerm α)
    (h : Derivation body Gamma (codedBelow (appendRelation a b n z) c d (suc n)))
    (hi : Derivation body Gamma (ltF i (suc n))) :
    Nonempty (Derivation body Gamma (existsOne (residueRelation a b n z i ⊓
      beta (c.relabel Sum.inl) (d.relabel Sum.inl) (i.relabel Sum.inl) (.var (.inr 0))))) := by
  have h := boundedElim _ i (suc n) h hi
  rw [instantiate,bindEmbedding,existsSubst,liftEmbedding,infSubst,atAppendIndex,betaSubst] at h
  simp only [liftSubst,liftBind,varBind] at h
  exact ⟨h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaExtensionSupportProof
