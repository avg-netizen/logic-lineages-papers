module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOrientedBezoutArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination
open InternalLinearCombinationSyntaxProof InternalBezoutExistenceTargets
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalAdditionCancellationProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaDivisionSyntaxProof
open InternalBetaTotalityProof InternalLinearCombinationZeroRemainderProof
open InternalPositiveUnfoldingSupportProof SourceComputabilityFormulaSupportProof
open InternalQuotientGapProof InternalBezoutCRTProof InternalBetaUniquenessProof
open InternalMultiplicationCommutativityProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem coprimeRename {α β : Type} (m a : OrdinaryArithmetic.Term α) (j : α → β) :
    (coprime m a).relabel j = coprime (m.relabel j) (a.relabel j) := by
  unfold coprime
  rw [InternalBinderTransportProof.actualUniversalRenaming]
  simp only [onEquality]
  change allOne (((arithmeticEmbedding.onFormula (divides (suc (.var (.inr 0))) (m.relabel Sum.inl))).relabel (Sum.map j id) ⊓
    (arithmeticEmbedding.onFormula (divides (suc (.var (.inr 0))) (a.relabel Sum.inl))).relabel (Sum.map j id)).imp
    ((eqn (suc (.var (.inr 0))) (suc z)).relabel (Sum.map j id))) = _
  simp only [dividesRename,eqnRelabel,sucRelabel,zRelabel,Term.relabel_relabel]
  rfl

/-- The two residues zero and one cannot both be below a positive modulus greater than one. -/
theorem unitGap (e k l : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn (suc (mul k (suc e))) (mul l (suc e))))) :
    Nonempty (Derivation body Gamma (eqn (suc e) one)) := by
  obtain ⟨h⟩ := h
  have hzero : Derivation body Gamma ((eqn e z).imp (eqn (suc e) one)) :=
    Derivation.implicationIntroduction (congSuc (Derivation.hypothesis List.mem_cons_self))
  have hsucc : Nonempty (Derivation body Gamma ((successorExists e).imp (eqn (suc e) one))) := by
    have hh : Nonempty (Derivation body (successorExists e :: Gamma) (eqn (suc e) one)) := by
      apply successorCases (successorExists e :: Gamma) e _ ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro β j Delta t hi ⟨he⟩
      simp only [eqnRelabel,sucRelabel,zRelabel]
      have hc := renameInto ⟨addHyp h (successorExists e)⟩ j Delta hi
      simp only [eqnRelabel,sucRelabel,mulRelabel] at hc
      obtain ⟨hc⟩ := hc
      let E := e.relabel j
      let K := k.relabel j
      let L := l.relabel j
      let M := suc E
      have ha : Derivation body Delta (eqn (mul L M) (add (mul K M) one)) :=
        trans (symm hc) (symm (trans (addSucc (mul K M) z) (congSuc (addZero (mul K M)))))
      have hb : Derivation body Delta (eqn (mul L M) (add (mul L M) z)) := symm (addZero _)
      have hr : Derivation body Delta (eqn (add one (suc t)) M) :=
        trans (oneAdd (suc t)) (symm (congSuc he))
      obtain ⟨hf⟩ := remainderUnique Delta (mul L M) M K L one z t E ha hb hr (leftZero M)
      exact ⟨Derivation.explosion (Derivation.implicationElimination (sucNeZero z) hf)⟩
    obtain ⟨hh⟩ := hh
    exact ⟨Derivation.implicationIntroduction hh⟩
  obtain ⟨hsucc⟩ := hsucc
  exact ⟨disjunctionElimination (zeroOrSuccessor e) hzero hsucc⟩

theorem dividesCases (Gamma : List (Formula α)) (d a : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides d a))))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (q : OrdinaryArithmetic.Term β),
      (∀ f ∈ Gamma, f.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (eqn (a.relabel j) (mul q (d.relabel j)))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  rw [divides,InternalFiniteBlocksBindingProof.actualOriginalBlockEmbedding] at h
  apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body α 1 Gamma _ psi h
  apply k (α ⊕ Fin 1) Sum.inl _ (.var (.inr 0))
  · intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  · rw [onEquality]
    exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem commonDivisorUnit (e m a u v : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (eqn (suc (mul u m)) (mul v a))))
    (hm : Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides (suc e) m))))
    (ha : Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides (suc e) a)))) :
    Nonempty (Derivation body Gamma (eqn (suc e) one)) := by
  apply dividesCases Gamma (suc e) m _ hm
  intro β j Delta q hi hq
  simp only [eqnRelabel,sucRelabel,zRelabel]
  have hc' := renameInto hc j Delta hi
  simp only [eqnRelabel,sucRelabel,mulRelabel] at hc'
  have ha' := renameInto ha j Delta hi
  rw [dividesRename,sucRelabel] at ha'
  apply dividesCases Delta (suc (e.relabel j)) (a.relabel j) _ ha'
  intro γ f Theta r hf hr
  simp only [eqnRelabel,sucRelabel,zRelabel]
  have hc'' := renameInto hc' f Theta hf
  simp only [eqnRelabel,sucRelabel,mulRelabel] at hc''
  have hq' := renameInto hq f Theta hf
  simp only [eqnRelabel,sucRelabel,mulRelabel] at hq'
  obtain ⟨hc''⟩ := hc''
  obtain ⟨hq'⟩ := hq'
  simp only [sucRelabel] at hr
  obtain ⟨hr⟩ := hr
  let U := (u.relabel j).relabel f
  let V := (v.relabel j).relabel f
  let Q := q.relabel f
  let E := (e.relabel j).relabel f
  apply unitGap E (mul U Q) (mul V r)
  exact ⟨InternalTagArithmeticSupportProof.trans (congSuc (trans (multiplicationAssociativity U Q (suc E)) (congMulLeft U (symm hq'))))
    (InternalTagArithmeticSupportProof.trans hc'' (InternalTagArithmeticSupportProof.trans (congMulLeft V hr) (symm (multiplicationAssociativity V r (suc E)))))⟩

theorem certificateCoprimality (m a u v : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (eqn (suc (mul u m)) (mul v a)))) :
    Nonempty (Derivation body Gamma (coprime m a)) := by
  let M := m.relabel (Sum.inl : α → α ⊕ Fin 1)
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let p := arithmeticEmbedding.onFormula (divides (suc x) M) ⊓
    arithmeticEmbedding.onFormula (divides (suc x) A)
  let Delta := p :: Gamma.map weaken
  have hi : ∀ f ∈ Gamma, f.relabel Sum.inl ∈ Delta := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have hc := renameInto h Sum.inl Delta hi
  simp only [eqnRelabel,sucRelabel,mulRelabel] at hc
  have hp : Derivation body Delta p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨he⟩ := commonDivisorUnit x M A (u.relabel Sum.inl) (v.relabel Sum.inl) hc
    ⟨Derivation.conjunctionLeft hp⟩ ⟨Derivation.conjunctionRight hp⟩
  unfold coprime
  rw [onEquality]
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction he)⟩

theorem actualCertificateCoprimality : InternalDivisibilityTargets.ActualCertificateCoprimality := by
  intro body α m a u v
  rw [onEquality]
  obtain ⟨h⟩ := certificateCoprimality (body := body) (Gamma := [eqn (suc (mul u m)) (mul v a)]) m a u v
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProof
