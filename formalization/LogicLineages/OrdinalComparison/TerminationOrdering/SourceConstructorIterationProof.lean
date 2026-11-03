module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationProof
open Source FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains CoherentConstructorLattice ExecutableDomainBottom SourceConstructorIteration

theorem bottomLeast : SourceConstructorIterationTargets.BottomLeast := by
  intro Symbol inst arity I M f τ P a
  exact ExecutableDomainBottomProof.least Symbol inst arity I τ.val P _

theorem sourceMonotone {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (above : Symbol → Symbol → Prop) [DecidableRel above] : Monotone (SourceConstructorOperatorProof.operator (I := I) above) := by
  intro M N hMN
  exact SourceConstructorOperatorProof.operatorMonotone Symbol inferInstance arity I above inferInstance M N hMN

theorem ascendingIteration : SourceConstructorIterationTargets.AscendingIteration := by
  intro Symbol inst arity I above dec n
  induction n with
  | zero => exact bottomLeast Symbol inst arity I _
  | succ n ih => exact sourceMonotone above ih

theorem monotoneIteration {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) [DecidableRel above] : Monotone (iterate I above) :=
  monotone_nat_of_le_succ (ascendingIteration Symbol inferInstance arity I above inferInstance)

theorem stableLater {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) [DecidableRel above]
    (k : Nat) (hk : iterate I above k=iterate I above (k+1)) : ∀ j,iterate I above (k+j)=iterate I above k := by
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Nat.add_succ,iterate,ih]
      exact hk.symm

theorem cardinalityStabilization : SourceConstructorIterationTargets.CardinalityStabilization := by
  intro Symbol inst arity I above dec
  by_contra h
  have hne : ∀ i,i ≤ fuel I → iterate I above i ≠ iterate I above (i+1) := by
    intro i hi he
    have h0 := stableLater I above i he (fuel I-i)
    have h1 := stableLater I above i he (fuel I+1-i)
    have e0 : i+(fuel I-i)=fuel I := by omega
    have e1 : i+(fuel I+1-i)=fuel I+1 := by omega
    rw [e0] at h0
    rw [e1] at h1
    exact h (h0.trans h1.symm)
  let seq : Fin (fuel I+1) → Constructors I := fun i => iterate I above i.val
  have hs : StrictMono seq := by
    intro i j hij
    have hi : i.val ≤ fuel I := by omega
    have hstep : iterate I above i.val < iterate I above (i.val+1) :=
      lt_iff_le_and_ne.mpr ⟨ascendingIteration Symbol inst arity I above dec i.val,hne i.val hi⟩
    exact lt_of_lt_of_le hstep (monotoneIteration I above (Nat.succ_le_of_lt hij))
  have hcard := Fintype.card_le_of_injective seq hs.injective
  simp only [Fintype.card_fin] at hcard
  change fuel I+1 ≤ fuel I at hcard
  omega

theorem actualFixedPoint : SourceConstructorIterationTargets.ActualFixedPoint := by
  intro Symbol inst arity I above dec
  exact (cardinalityStabilization Symbol inst arity I above dec).symm

theorem iterateBelow {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat}
    (I : Input Symbol arity) (above : Symbol → Symbol → Prop) [DecidableRel above]
    (M : Constructors I) (hM : SourceConstructorOperatorProof.operator above M ≤ M) :
    ∀ n,iterate I above n ≤ M := by
  intro n
  induction n with
  | zero => exact bottomLeast Symbol inferInstance arity I M
  | succ n ih => exact le_trans (sourceMonotone above ih) hM

theorem leastPreFixedPoint : SourceConstructorIterationTargets.LeastPreFixedPoint := by
  intro Symbol inst arity I above dec M hM
  exact iterateBelow I above M hM (fuel I)

theorem eventualConstancy : SourceConstructorIterationTargets.EventualConstancy := by
  intro Symbol inst arity I above dec n hn
  have he := stableLater I above (fuel I) (cardinalityStabilization Symbol inst arity I above dec) (n-fuel I)
  have hsum : fuel I+(n-fuel I)=n := by omega
  rw [hsum] at he
  exact he

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceConstructorIterationProof
