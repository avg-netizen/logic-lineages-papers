module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalAdditionCancellationProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaDivisionSyntaxProof InternalBetaWitness
open InternalDivisibilityProof InternalBezoutExistenceTargets InternalLinearCombinationSyntaxProof
open InternalCoprimeMultiple InternalCoprimeMultipleSyntaxProof InternalCoprimeMultipleBoundedProof
open InternalCoprimeMultipleSupportProof InternalBetaModulusCoprimality
open InternalBetaModulusCoprimalityArithmeticProof InternalBetaModulusCoprimalityExistenceProof
open InternalPositiveUnfoldingSupportProof InternalBinderTransportSyntaxProof
open InternalQuotientGapProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem differenceMultiplesRename {α β : Type} (b n : OrdinaryArithmetic.Term α) (j : α → β) :
    (differenceMultiples b n).relabel j = differenceMultiples (b.relabel j) (n.relabel j) := by
  unfold differenceMultiples
  rw [dividesBelowRename]
  rfl

theorem boundedDifference (b n w : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (differenceMultiples b n)))
    (hw : Nonempty (Derivation body Gamma (ltF w n))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (InternalLinearCombination.divides (suc w) b))) := by
  obtain ⟨hc⟩ := hc
  obtain ⟨hw⟩ := hw
  have hd := boundedElim (arithmeticEmbedding.onFormula
    (InternalLinearCombination.divides (suc (.var (.inr 0))) (b.relabel Sum.inl))) w n hc hw
  simp only [instantiate,bindEmbedding,dividesSubst,sucSubst,varBind,liftBind] at hd
  exact ⟨hd⟩

theorem orderedCoprimality (b i j n : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (differenceMultiples (suc b) n)))
    (hi : Nonempty (Derivation body Gamma (ltF i j)))
    (hj : Nonempty (Derivation body Gamma (ltF j n))) :
    Nonempty (Derivation body Gamma (coprime (modulus (suc b) j) (modulus (suc b) i))) := by
  apply orderCases Gamma i j _ hi
  intro β f Delta w hf he
  simp only [coprimeRename,modulusRename,sucRelabel]
  have hc' := renameInto hc f Delta hf
  rw [differenceMultiplesRename,sucRelabel] at hc'
  have hj' := renameInto hj f Delta hf
  rw [orderRename] at hj'
  obtain ⟨he⟩ := he
  let B := b.relabel f
  let I := i.relabel f
  let J := j.relabel f
  let N := n.relabel f
  have hwj : Nonempty (Derivation body Delta (ltF w J)) := by
    apply actualOriginalOrderIntroduction body β Delta w J I
    rw [onEquality]
    exact ⟨trans (trans (addSucc w I) (trans (congSuc (commutativity w I)) (symm (addSucc I w)))) he⟩
  obtain ⟨ht⟩ := actualOriginalOrderTransitivity body β w J N
  obtain ⟨hwj⟩ := hwj
  obtain ⟨hj'⟩ := hj'
  have hwn := Derivation.implicationElimination (weakenClosed ht Delta) (Derivation.conjunctionIntroduction hwj hj')
  have hd := boundedDifference (suc B) N w hc' ⟨hwn⟩
  obtain ⟨hp⟩ := differenceCoprimality B I w hd
  have hm : Derivation body Delta (eqn (modulus (suc B) (add I (suc w))) (modulus (suc B) J)) :=
    congSuc (congMulRight (suc B) (congSuc he))
  exact coprimeSymmetry _ _ ⟨coprimeCongruence _ _ _ hm hp⟩

theorem actualBetaModulusPairwise : InternalBetaModulusCoprimalityTargets.ActualBetaModulusPairwise := by
  intro body α b n
  let Gamma := [differenceMultiples (suc b) n]
  let j : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let N := n.relabel (Sum.inl : α → α ⊕ Fin 1)
  let Delta := ltF j N :: Gamma.map weaken
  have h0 : Nonempty (Derivation body Gamma (differenceMultiples (suc b) n)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h1 := renameInto h0 Sum.inl Delta (by
    intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  rw [differenceMultiplesRename,sucRelabel] at h1
  let i : OrdinaryArithmetic.Term ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let J := j.relabel (Sum.inl : α ⊕ Fin 1 → (α ⊕ Fin 1) ⊕ Fin 1)
  let Theta := ltF i J :: Delta.map weaken
  have h2 := renameInto h1 Sum.inl Theta (by
    intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  rw [differenceMultiplesRename,sucRelabel] at h2
  have hj0 : Nonempty (Derivation body Delta (ltF j N)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hj := renameInto hj0 Sum.inl Theta (by
    intro f hf; exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  rw [orderRename] at hj
  have hi : Nonempty (Derivation body Theta (ltF i J)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hp⟩ := orderedCoprimality ((b.relabel Sum.inl).relabel Sum.inl) i J (N.relabel Sum.inl) h2 hi hj
  apply Nonempty.intro
  apply Derivation.implicationIntroduction
  unfold InternalBoundedCRT.pairwiseBelow coprimeBelow bounded betaFamily
  simp only [sucRelabel,mulRelabel,Term.relabel_relabel]
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  apply Derivation.universalIntroduction
  apply Derivation.implicationIntroduction
  simpa only [Theta,Delta,Gamma,J,j,i,N,modulus,Term.relabel_relabel,mapInl,Term.relabel] using hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaModulusCoprimalityProof
