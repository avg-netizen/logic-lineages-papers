module
public import LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCountTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCount
open OrdinalComparison FieldComparison PreparedProjection
open ActualMixedRowLeadingAnnotations ActualZeroClassReplacement ActualRankedRowColumns
open ActualZeroClassCohortTransfer ActualCountOriginDispositions ActualWeightedReadNormalization
open SelectedCountOnlyClass (prefixTarget)
open InnerTerminationTargets (Disposition lowerTerm)

private theorem groupedAppend (xs ys : List Read) :
    groupedWeights (xs ++ ys) = groupedWeights xs + groupedWeights ys := by
  induction xs with
  | nil => simp [groupedWeights]
  | cons rd xs ih =>
      change Finsupp.single rd.1.2 rd.1.1 + groupedWeights (xs ++ ys) =
        (Finsupp.single rd.1.2 rd.1.1 + groupedWeights xs) + groupedWeights ys
      rw [ih,add_assoc]

private theorem rankedCountAppend (r : Nat) (xs ys : List Read) :
    (rankedRow r 0 (xs ++ ys)).count =
      (rankedRow r 0 xs).count + (rankedRow r 0 ys).count := by
  apply Finsupp.ext
  intro k
  change groupedWeights (xs ++ ys) (countOperand r k) =
    (groupedWeights xs + groupedWeights ys) (countOperand r k)
  rw [groupedAppend]

private theorem rankedCountNil (r : Nat) : (rankedRow r 0 []).count = 0 := by
  apply Finsupp.ext
  intro k
  change groupedWeights [] (countOperand r k) = 0
  rfl

private theorem rankedCountSingleton (r : Nat) (k : CountKey r) (a : Int) (n : Nat) :
    (rankedRow r 0 [((a,countOperand r k),n)]).count = Finsupp.single k a := by
  classical
  apply Finsupp.ext
  intro j
  change groupedWeights [((a,countOperand r k),n)] (countOperand r j) =
    Finsupp.single k a j
  simp only [groupedWeights,add_zero,Finsupp.single_apply,(countOperand r).injective.eq_iff]

private theorem rankedAnchor {r : Nat} (anchor : SurvivingPrefix) (x₀ : Fin r)
    (q : NONote × NONote) (h : anchor.rank = x₀.val ∧ (anchor.lam,anchor.eta) = q)
    (a : Int) :
    (rankedRow r 0 [anchorRead anchor a]).count = Finsupp.single (q,x₀) a := by
  have hr : anchorRead anchor a = ((a,countOperand r (q,x₀)),anchor.count) := by
    rw [← h.2]
    change ((a,LowerOperand.count anchor.rank anchor.lam anchor.eta),anchor.count) =
      ((a,LowerOperand.count x₀.val anchor.lam anchor.eta),anchor.count)
    rw [h.1]
  rw [hr,rankedCountSingleton]

private theorem rankedSubtraction {r : Nat} (anchor p : SurvivingPrefix)
    (x₀ : Fin r) (h : anchor.rank = x₀.val) (j : Nat) :
    (rankedRow r 0 [subtractRead anchor p j]).count =
      Finsupp.single ((anchor.lam,anchor.eta + (p.lam - p.eta)),x₀) (-p.weight) := by
  have hr : subtractRead anchor p j =
      ((-p.weight,countOperand r ((anchor.lam,anchor.eta + (p.lam - p.eta)),x₀)),j) := by
    change ((-p.weight,LowerOperand.count anchor.rank anchor.lam (anchor.eta + (p.lam-p.eta))),j) =
      ((-p.weight,LowerOperand.count x₀.val anchor.lam (anchor.eta + (p.lam-p.eta))),j)
    rw [h]
  rw [hr,rankedCountSingleton]

private theorem singleNeg {r : Nat} (k : CountKey r) (a : Int) :
    Finsupp.single k (-a) = -(Finsupp.single k a) := by
  classical
  apply Finsupp.ext
  intro j
  by_cases he : k = j <;> simp [Finsupp.single_apply,he]

private theorem groupedHead (f : Nat → Nat) (ρ : Nat → Nat) {r : Nat}
    (anchor : Option SurvivingPrefix) (x₀ : Fin r) (q : NONote × NONote)
    (anchorAt : AnchorAt anchor x₀ q) (entry : Origin) (d : CountDisposition) (out : List Read)
    (outcome : OriginOutcome f ρ anchor entry d out) :
    (rankedRow r 0 out).count = d.term x₀ q entry.1.1.1 := by
  obtain ⟨⟨⟨a,op⟩,v⟩,ann⟩ := entry
  cases op <;> cases ann <;> simp only [OriginOutcome] at outcome
  all_goals try exact outcome.2.elim
  rename_i rank lam mu i E κ
  have head := outcome.2
  by_cases identity : i = 0
  · simp only [if_pos identity] at head
    obtain ⟨_,rfl,rfl⟩ := head
    exact rankedCountNil r
  · by_cases long : shortGapLength lam (prefixTarget mu) = 0
    · simp only [if_neg identity,if_pos long] at head
      obtain ⟨pivot,hp,_,_,tail⟩ := head
      have ha := anchorAt pivot hp
      by_cases equalRank : rank = pivot.rank
      · simp only [if_pos equalRank] at tail
        obtain ⟨_,rfl,rfl⟩ := tail
        exact rankedAnchor pivot x₀ q ha a
      · simp only [if_neg equalRank] at tail
        obtain ⟨_,j,_,_,rfl,rfl⟩ := tail
        let p : SurvivingPrefix := ⟨rank,lam,prefixTarget mu,a,i⟩
        change (rankedRow r 0 ([anchorRead pivot a] ++ [subtractRead pivot p j])).count =
          (Disposition.transferred (some (pivot.lam,pivot.eta + (lam - prefixTarget mu))) κ).term x₀ q a
        rw [rankedCountAppend,rankedAnchor pivot x₀ q ha a,rankedSubtraction pivot p x₀ ha.1 j]
        simp only [p,Disposition.term,lowerTerm,singleNeg,sub_eq_add_neg]
    · simp only [if_neg identity,if_neg long] at head
      obtain ⟨_,rfl,rfl⟩ := head
      exact rankedCountNil r

private theorem groupedLedger (f : Nat → Nat) (ρ : Nat → Nat) {r : Nat}
    (anchor : Option SurvivingPrefix) (x₀ : Fin r) (q : NONote × NONote)
    (anchorAt : AnchorAt anchor x₀ q) (origins : List Origin)
    (ledger : List (Origin × CountDisposition)) (out : List Read)
    (disposed : DisposedOrigins f ρ anchor origins ledger out) :
    (rankedRow r 0 out).count = movedCountTerms x₀ q ledger := by
  induction disposed with
  | nil => exact rankedCountNil r
  | @cons entry _ d tail first rest outcome _ ih =>
      change (rankedRow r 0 (first ++ rest)).count =
        d.term x₀ q entry.1.1.1 + movedCountTerms x₀ q tail
      rw [rankedCountAppend,groupedHead f ρ anchor x₀ q anchorAt entry d first outcome,ih]

theorem exactGroupedMovedCount : ExactGroupedMovedCount := by
  intro f ρ C r xs annotations anchor x₀ q ledger moved hAnchor hDisposed
  exact groupedLedger f ρ anchor x₀ q hAnchor _ ledger moved hDisposed

end LogicLineages.PermittedControl.ActualZeroClassGroupedMovedCount
