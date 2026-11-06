module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationZeroRemainderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination
open InternalLinearCombinationSyntaxProof InternalLinearCombinationArithmeticProof InternalLinearCombinationProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalAdditionCancellationProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaDivisionSyntaxProof
open InternalBetaTotalityProof InternalLeastNumberProof InternalLeastNumberSyntaxProof
open InternalLinearCombinationZeroRemainderProof SourceComputabilityFormulaSupportProof
open InternalBinderTransportProof InternalTermSubstitutionSyntaxProof InternalBinderTransportSyntaxProof
open InternalBetaBoundaryProof InternalQuotientComparisonSyntaxProof
open InternalPositiveUnfoldingSupportProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def combinationCongruence (a b r s : OrdinaryArithmetic.Term α)
    (he : Derivation body Gamma (eqn r s)) (hc : Derivation body Gamma (cf a b r)) :
    Derivation body Gamma (cf a b s) := by
  let p := cf (a.relabel (Sum.inl : α → α ⊕ Fin 1)) (b.relabel Sum.inl) (.var (.inr 0))
  have hp : Derivation body Gamma (instantiate p (emb r)) := by
    simp only [p,combinationInstantiate,liftBind,varBind]
    exact hc
  have h := Derivation.equalityElimination p (emb r) (emb s) he hp
  simpa only [p,combinationInstantiate,liftBind,varBind] using h

def excludePositive (a b e t : OrdinaryArithmetic.Term α)
    (hl : Derivation body Gamma (lower a b e))
    (ht : Derivation body Gamma (ltF t e))
    (hc : Derivation body Gamma (cf a b (suc t))) : Derivation body Gamma ⊥ := by
  have h := Derivation.universalElimination (emb t) hl
  rw [belowElimSyntax,familyInstantiate] at h
  exact Derivation.implicationElimination (Derivation.implicationElimination h ht) hc

theorem zeroRemainder (a b e r g : OrdinaryArithmetic.Term α)
    (hl : Nonempty (Derivation body Gamma (lower a b e)))
    (hc : Nonempty (Derivation body Gamma (cf a b r)))
    (hb : Nonempty (Derivation body Gamma (eqn (add r (suc g)) (suc e)))) :
    Nonempty (Derivation body Gamma (eqn r z)) := by
  have hr : Nonempty (Derivation body Gamma ((successorExists r).imp (eqn r z))) := by
    let Delta := successorExists r :: Gamma
    have hi : ∀ p ∈ Gamma, p ∈ Delta := fun _ hp => List.mem_cons_of_mem _ hp
    have hh : Nonempty (Derivation body Delta (eqn r z)) := by
      apply successorCases Delta r _ ⟨Derivation.hypothesis List.mem_cons_self⟩
      intro β j Theta t ht ⟨he⟩
      have hj : ∀ p ∈ Gamma, p.relabel j ∈ Theta := fun p hp => ht p (hi p hp)
      have hl' := renameInto hl j Theta hj
      rw [lowerRename] at hl'
      obtain ⟨hl'⟩ := hl'
      have hc' := renameInto hc j Theta hj
      rw [combinationRename] at hc'
      obtain ⟨hc'⟩ := hc'
      have hb' := renameInto hb j Theta hj
      simp only [eqnRelabel,addRelabel,sucRelabel] at hb'
      obtain ⟨hb'⟩ := hb'
      have ht' : Nonempty (Derivation body Theta (ltF t (e.relabel j))) := by
        apply actualOriginalOrderIntroduction body β Theta t (e.relabel j) (g.relabel j)
        rw [onEquality]
        exact ⟨cancelSuc (trans (symm (leftSuccessor t (suc (g.relabel j))))
          (trans (InternalMultiplicationLawsProof.congAddRight _ (symm he)) hb'))⟩
      obtain ⟨ht'⟩ := ht'
      exact ⟨Derivation.explosion (excludePositive _ _ _ _ hl' ht'
        (combinationCongruence _ _ _ _ he hc'))⟩
    obtain ⟨hh⟩ := hh
    exact ⟨Derivation.implicationIntroduction hh⟩
  obtain ⟨hr⟩ := hr
  exact ⟨disjunctionElimination (zeroOrSuccessor r)
    (Derivation.implicationIntroduction (Derivation.hypothesis List.mem_cons_self)) hr⟩

/-- At beta index zero the original positive modulus is exactly succ e. -/
def modulusZero (e : OrdinaryArithmetic.Term α) :
    Derivation body Gamma (eqn (InternalBetaWitness.modulus e z) (suc e)) :=
  congSuc (multiplicationLeftOne e)

theorem minimumDividesFirst (a b e : OrdinaryArithmetic.Term α)
    (hc : Nonempty (Derivation body Gamma (cf a b (suc e))))
    (hl : Nonempty (Derivation body Gamma (lower a b e))) :
    Nonempty (Derivation body Gamma (arithmeticEmbedding.onFormula (divides (suc e) a))) := by
  obtain ⟨ht⟩ := InternalBetaTotalityProof.actualBetaTotality body α a e z
  apply remainderCases Gamma a e z _ ⟨weakenClosed ht Gamma⟩
  intro β j Delta r hi hbeta
  rw [dividesRename,sucRelabel]
  have hc' := renameInto hc j Delta hi
  rw [combinationRename,sucRelabel] at hc'
  have hl' := renameInto hl j Delta hi
  rw [lowerRename] at hl'
  simp only [zRelabel] at hbeta
  apply InternalBetaDivisionProof.betaCases Delta (a.relabel j) (e.relabel j) z r _ hbeta
  intro γ k Theta q g hk he
  rw [dividesRename,sucRelabel]
  have hc'' := renameInto hc' k Theta hk
  rw [combinationRename,sucRelabel] at hc''
  have hl'' := renameInto hl' k Theta hk
  rw [lowerRename] at hl''
  rw [InternalBetaDivisionProof.equationEmbedding] at he
  simp only [zRelabel] at he
  obtain ⟨he⟩ := he
  let A := (a.relabel j).relabel k
  let B := (b.relabel j).relabel k
  let E := (e.relabel j).relabel k
  let R := r.relabel k
  have hdiv : Derivation body Theta (eqn A (add (mul q (suc E)) R)) :=
    trans (Derivation.conjunctionLeft he)
      (InternalMultiplicationLawsProof.congAddRight R (congMulLeft q (modulusZero E)))
  have hbound : Derivation body Theta (eqn (add R (suc g)) (suc E)) :=
    trans (Derivation.conjunctionRight he) (modulusZero E)
  have hrem := remainderClosure A B (suc E) q R hc'' ⟨hdiv⟩
  obtain ⟨hz⟩ := zeroRemainder A B E R g hl'' hrem ⟨hbound⟩
  apply dividesIntroduction (suc E) A q
  exact ⟨trans hdiv (trans (congAddLeft _ hz) (addZero _))⟩
theorem lowerSymmetry (a b e : OrdinaryArithmetic.Term α)
    (hl : Nonempty (Derivation body Gamma (lower a b e))) :
    Nonempty (Derivation body Gamma (lower b a e)) := by
  let A := a.relabel (Sum.inl : α → α ⊕ Fin 1)
  let B := b.relabel (Sum.inl : α → α ⊕ Fin 1)
  let E := e.relabel (Sum.inl : α → α ⊕ Fin 1)
  let x : OrdinaryArithmetic.Term (α ⊕ Fin 1) := .var (.inr 0)
  let Delta := cf B A (suc x) :: ltF x E :: Gamma.map weaken
  have hi : ∀ p ∈ Gamma, p.relabel Sum.inl ∈ Delta := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  have hl' := renameInto hl Sum.inl Delta hi
  rw [lowerRename] at hl'
  obtain ⟨hl'⟩ := hl'
  obtain ⟨hc⟩ := combinationSymmetry (body := body) (Gamma := Delta) B A (suc x)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf : Derivation body Delta ⊥ := excludePositive A B E x hl'
    (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) hc
  exact ⟨Derivation.universalIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction hf))⟩

theorem actualMinimumDivides : InternalLinearCombinationTargets.ActualMinimumDivides := by
  intro body α a b e
  change Nonempty (Derivation body [] ((instantiate (minP (pf a b)) (emb e)).imp _))
  rw [minInstantiate,familyInstantiate]
  let Gamma := [cf a b (suc e) ⊓ lower a b e]
  have h : Derivation body Gamma (cf a b (suc e) ⊓ lower a b e) := Derivation.hypothesis List.mem_cons_self
  have hc := Derivation.conjunctionLeft h
  have hl := Derivation.conjunctionRight h
  obtain ⟨ha⟩ := minimumDividesFirst a b e ⟨hc⟩ ⟨hl⟩
  have hc' := combinationSymmetry a b (suc e) ⟨hc⟩
  have hl' := lowerSymmetry a b e ⟨hl⟩
  obtain ⟨hb⟩ := minimumDividesFirst b a e hc' hl'
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction ha hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBezoutExistenceProof
