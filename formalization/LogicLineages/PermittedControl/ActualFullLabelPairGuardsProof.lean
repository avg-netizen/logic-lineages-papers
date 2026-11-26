module
public import LogicLineages.PermittedControl.ActualFullLabelPairGuardsTargets
import LogicLineages.PermittedControl.ActualFullLabelPairGuardsLowerProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighOrientationProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighValueProof
import LogicLineages.PermittedControl.ActualSignedOrdinaryPairHighPaidProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullLabelPairGuards
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualFullValueLabels (Label ActualLabel)
open ActualSignedOrdinaryPairHigh (minimum orientedMinimum guardedFields exactOrientedSignedPair
  exactSignedPairValue)

private theorem sameRead (f θ : Nat → Nat) (l : Label) (u v : Nat)
    (h : ActualLabel f θ l u) (h' : ActualLabel f θ l v) : u = v :=
  Option.some.inj (Option.some.inj (h.2.2.symm.trans h'.2.2))

private theorem labelActual (f θ : Nat → Nat) (l : Label) (v : Nat)
    (proper : ProperField l.field) (actual : LowerOperandActual f θ (.ordinary l.rank l.field) v) :
    ActualLabel f θ l v := ⟨proper,actual,(preparedTiedProjection.1 f θ _ _).mpr actual⟩

private theorem knownOutcome (f θ : Nat → Nat) (p : Pair) (a : Answer) (u v : Nat)
    (hu : ActualLabel f θ p.1 u) (hv : ActualLabel f θ p.2 v) :
    ActualOutcome f θ p a ↔ numericalComparison u v = a.code := by
  constructor
  · rintro ⟨u',v',au,av,cmp⟩
    rw [sameRead f θ p.1 u' u au hu,sameRead f θ p.2 v' v av hv] at cmp
    exact cmp
  · intro cmp
    exact ⟨u,v,hu,hv,cmp⟩

private theorem payAt (B : Nat) (ρ : Nat → Nat) (top z : Nat) (p : Pair)
    (ready : Ready B ρ top p) (paid : PaidUpdate B ρ top z p) :
    cost B p ≤ min ((Function.update ρ top z) p.1.rank) ((Function.update ρ top z) p.2.rank) := by
  have rankPay (r : Nat) (leTop : r ≤ top) (lower : r < top → cost B p ≤ ρ r) :
      cost B p ≤ (Function.update ρ top z) r := by
    rcases leTop.eq_or_lt with eq | lt
    · subst r
      simpa only [Function.update_self] using paid.1
    · rw [Function.update_of_ne (ne_of_lt lt)]
      exact lower lt
  exact le_min (rankPay _ ready.1 ready.2.2.2.2.1)
    (rankPay _ ready.2.1 ready.2.2.2.2.2)

private theorem paidValues (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (top z : Nat) (p : Pair) (ready : Ready B ρ top p)
    (paid : PaidUpdate B ρ top z p) :
    ∃ u v : Nat, ActualLabel f (Function.update ρ top z) p.1 u ∧
      ActualLabel f (Function.update ρ top z) p.2 v := by
  let θ := Function.update ρ top z
  have tail : minimum B p.1.field p.2.field ≤ min (θ p.1.rank) (θ p.2.rank) :=
    (le_max_left _ _).trans (payAt B ρ top z p ready paid)
  obtain ⟨_,_,u,v,first,second,_⟩ := guardedFields f B selected p.1.field p.2.field
    ready.2.2.1 ready.2.2.2.1 θ p.1.rank p.2.rank tail
  exact ⟨u,v,labelActual f θ p.1 u ready.2.2.1 first,
    labelActual f θ p.2 v ready.2.2.2.1 second⟩

private theorem orientationPaid (B : Nat) (p : Pair) :
    orientedMinimum B p.1.field p.2.field p.1.rank p.2.rank ≤ cost B p := by
  unfold orientedMinimum cost
  split
  · exact le_max_right _ _
  · exact le_max_left _ _

private theorem sourceTop (f θ : Nat → Nat) (p : Pair) (a : Answer) (u v : Nat)
    (hu : ActualLabel f θ p.1 u) (hv : ActualLabel f θ p.2 v) :
    ActualSignedOrdinaryPairHigh.source f θ p.1.field p.2.field p.1.rank p.2.rank
      (topRequest a).1 (topRequest a).2 true ↔ ActualOutcome f θ p a := by
  have nonzero : (topRequest a).1 ≠ 0 := by cases a <;> decide
  have one := exactSignedPairValue f θ p.1.field p.2.field p.1.rank p.2.rank
    u v (topRequest a).1 nonzero hu.2.1 hv.2.1 (topRequest a).2 true
  apply one.trans
  refine Iff.trans ?_ (knownOutcome f θ p a u v hu hv).symm
  cases a <;> simp [topRequest,ActualSignedOrdinaryPairHigh.request,
    ActualSignedOrdinaryPairHigh.wantedBit,Answer.code]

private theorem belowCase (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (top : Nat) (p : Pair) (ready : Ready B ρ top p)
    (below : p.maximum < top) (a : Answer) :
    let g := lowerPacket p a
    PreparedInput g.1 g.2 ∧ (∃ ν : Nat → Nat, PreparedTableTied f top ρ g.1 ν) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top ρ g.1 ν →
        ∀ z : Nat, PaidUpdate B ρ top z p →
          ((g.2.eval (Function.update ν 0 z)) ↔ ActualOutcome f (Function.update ρ top z) p a) := by
  let rs := (lowerPacket p a).1
  have smallF : p.1.rank < top := (le_max_left _ _).trans_lt below
  have smallG : p.2.rank < top := (le_max_right _ _).trans_lt below
  have own : minimum B p.1.field p.2.field ≤ min (ρ p.1.rank) (ρ p.2.rank) :=
    (le_max_left _ _).trans (le_min (ready.2.2.2.2.1 smallF) (ready.2.2.2.2.2 smallG))
  obtain ⟨_,_,u,v,hu,hv,_⟩ := guardedFields f B hf p.1.field p.2.field
    ready.2.2.1 ready.2.2.2.1 ρ p.1.rank p.2.rank own
  refine ⟨lowerShape p a,?_,?_⟩
  · let ν : Nat → Nat := fun n => if n = 1 then u else v
    refine ⟨ν,?_⟩
    intro j used
    have lit : j < 2 := used
    cases j with
    | zero => exact ⟨smallF,hu⟩
    | succ n =>
        have eq : n = 0 := by omega
        subst n
        exact ⟨smallG,hv⟩
  · intro ν fit z _
    let θ := Function.update ρ top z
    have rawF : θ p.1.rank = ρ p.1.rank :=
      Function.update_of_ne (ne_of_lt smallF) z ρ
    have rawG : θ p.2.rank = ρ p.2.rank :=
      Function.update_of_ne (ne_of_lt smallG) z ρ
    have left : LowerOperandActual f ρ (.ordinary p.1.rank p.1.field) (ν 1) := (fit 0 (by change 0 < 2; decide)).2
    have right : LowerOperandActual f ρ (.ordinary p.2.rank p.2.field) (ν 2) := (fit 1 (by change 1 < 2; decide)).2
    have left' : LowerOperandActual f θ (.ordinary p.1.rank p.1.field) (ν 1) := by
      change ClosedOrdinaryValueDomain p.1.field (θ p.1.rank) ∧ FieldValue f p.1.field (θ p.1.rank) (ν 1)
      rw [rawF]
      exact left
    have right' : LowerOperandActual f θ (.ordinary p.2.rank p.2.field) (ν 2) := by
      change ClosedOrdinaryValueDomain p.2.field (θ p.2.rank) ∧ FieldValue f p.2.field (θ p.2.rank) (ν 2)
      rw [rawG]
      exact right
    have lhs := lowerMeaning a (Function.update ν 0 z)
    change (lowerFormula a).eval (Function.update ν 0 z) ↔ ActualOutcome f θ p a
    exact (by simpa only [Function.update_of_ne (by decide : (1 : Nat) ≠ 0),
      Function.update_of_ne (by decide : (2 : Nat) ≠ 0)] using lhs :
        (lowerFormula a).eval (Function.update ν 0 z) ↔ numericalComparison (ν 1) (ν 2) = a.code).trans
      (knownOutcome f θ p a (ν 1) (ν 2) (labelActual f θ p.1 _ ready.2.2.1 left')
        (labelActual f θ p.2 _ ready.2.2.2.1 right')).symm

private theorem topCase (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (top : Nat) (p : Pair) (ready : Ready B ρ top p)
    (greatest : p.maximum = top) (a : Answer) :
    let g := topPacket p a
    PreparedInput g.1 g.2 ∧ (∃ ν : Nat → Nat, PreparedTableTied f top ρ g.1 ν) ∧
      ∀ (ν : Nat → Nat), PreparedTableTied f top ρ g.1 ν →
        ∀ z : Nat, PaidUpdate B ρ top z p →
          ((g.2.eval (Function.update ν 0 z)) ↔ ActualOutcome f (Function.update ρ top z) p a) := by
  let being := orientedMinimum B p.1.field p.2.field p.1.rank p.2.rank
  have lowPay :
      if p.1.rank = p.2.rank then True else being ≤ ρ (min p.1.rank p.2.rank) := by
    rcases lt_trichotomy p.1.rank p.2.rank with lt | eq | gt
    · rw [if_neg (ne_of_lt lt),min_eq_left lt.le]
      exact (orientationPaid B p).trans (ready.2.2.2.2.1 (lt.trans_le ready.2.1))
    · rw [if_pos eq]
      trivial
    · rw [if_neg (ne_of_gt gt),min_eq_right gt.le]
      exact (orientationPaid B p).trans (ready.2.2.2.2.2 (gt.trans_le ready.1))
  have nonzero : (topRequest a).1 ≠ 0 := by cases a <;> decide
  have compared := exactOrientedSignedPair f B hf p.1.field p.2.field ready.2.2.1 ready.2.2.2.1
    ρ p.1.rank p.2.rank (topRequest a).1 nonzero (topRequest a).2 true lowPay
  have maxEq : max p.1.rank p.2.rank = top := greatest
  obtain ⟨shape,⟨ν,tie⟩,point⟩ := compared
  refine ⟨shape,⟨ν,?_⟩,?_⟩
  · simpa only [maxEq,topPacket] using tie
  · intro μ fit z paid
    have paidInput :
        if p.1.rank = p.2.rank then being ≤ z else ρ (min p.1.rank p.2.rank) < z := by
      rcases lt_trichotomy p.1.rank p.2.rank with lt | eq | gt
      · rw [if_neg (ne_of_lt lt),min_eq_left lt.le]
        exact paid.2.1 (lt.trans_le ready.2.1)
      · rw [if_pos eq]
        exact (orientationPaid B p).trans paid.1
      · rw [if_neg (ne_of_gt gt),min_eq_right gt.le]
        exact paid.2.2 (gt.trans_le ready.1)
    have rawFit : PreparedTableTied f (max p.1.rank p.2.rank) ρ (topPacket p a).1 μ := by
      simpa only [maxEq] using fit
    have check := point μ rawFit z paidInput
    have paidWitness := paidValues f B hf ρ top z p ready paid
    obtain ⟨u,v,hu,hv⟩ := paidWitness
    have current :
        (topPacket p a).2.eval (Function.update μ 0 z) ↔
          ActualSignedOrdinaryPairHigh.source f (Function.update ρ top z)
            p.1.field p.2.field p.1.rank p.2.rank (topRequest a).1 (topRequest a).2 true := by
      simpa only [maxEq,topPacket] using check
    exact current.trans (sourceTop f (Function.update ρ top z) p a u v hu hv)

theorem exactFullLabelPairGuard : ExactFullLabelPairGuard := by
  intro f B selected ρ top p ready a
  by_cases below : p.maximum < top
  · simpa only [packet,if_pos below] using belowCase f B selected ρ top p ready below a
  · have eq : p.maximum = top :=
      le_antisymm (max_le ready.1 ready.2.1) (Nat.le_of_not_lt below)
    simpa only [packet,if_neg below] using topCase f B selected ρ top p ready eq a

theorem exactActualPairHasOutcome : ExactActualPairHasOutcome := by
  intro f B selected ρ top z p ready paid
  obtain ⟨u,v,hu,hv⟩ := paidValues f B selected ρ top z p ready paid
  rcases lt_trichotomy u v with lt | eq | gt
  · exact ⟨.less,by simp [choices],u,v,hu,hv,by simp [numericalComparison,Answer.code,lt]⟩
  · subst v
    exact ⟨.equal,by simp [choices],u,u,hu,hv,by simp [numericalComparison,Answer.code]⟩
  · have nl : ¬ u < v := not_lt_of_ge gt.le
    have ne : u ≠ v := ne_of_gt gt
    exact ⟨.greater,by simp [choices],u,v,hu,hv,by simp [numericalComparison,Answer.code,nl,ne]⟩

end LogicLineages.PermittedControl.ActualFullLabelPairGuards
