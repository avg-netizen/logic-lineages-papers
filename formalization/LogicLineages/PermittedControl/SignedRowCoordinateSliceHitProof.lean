module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowCoordinateSlice
open PreparedProjection FiniteStripCollectorRecovery
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)

private theorem tailHit (t : WeightedOperand) (hits : List (Nat × Nat))
    (tail : Result LowerOperand) (out : Residual LowerOperand)
    (h : step t (some (some hits)) tail = some (some out)) :
    ∃ before : Residual LowerOperand, tail = some (some before) ∧
      step t (some (some hits)) (some (some before)) = some (some out) := by
  cases tail with
  | none => simp [step] at h
  | some content =>
    cases content with
    | none => simp [step] at h
    | some before => exact ⟨before,rfl,h⟩

private theorem denotesCons (f ρ : Nat → Nat) (m : Nat) (c : Int)
    (t : WeightedOperand) (terms : List WeightedOperand) :
    denotes f ρ m c (t :: terms) ↔
      ∃ v, LowerOperandActual f ρ t.2 v ∧ lowerOperandRead f ρ t.2 = some (some v) ∧
        denotes f ρ m (c + t.1 * (v : Int)) terms := by
  constructor
  · rintro ⟨values,reads,congruence⟩
    cases values with
    | nil => exact False.elim reads
    | cons v vs =>
      obtain ⟨actual,read,more⟩ := reads
      refine ⟨v,actual,read,vs,more,?_⟩
      change (m : Int) ∣ c + (t.1 * (v : Int) + actualSum terms vs) at congruence
      simpa only [add_assoc] using congruence
  · rintro ⟨v,actual,read,vs,reads,congruence⟩
    refine ⟨v :: vs,⟨actual,read,reads⟩,?_⟩
    change (m : Int) ∣ c + (t.1 * (v : Int) + actualSum terms vs)
    simpa only [add_assoc] using congruence

private theorem denotesPaid (f ρ : Nat → Nat) (m : Nat) (c : Int)
    (t : WeightedOperand) (terms : List WeightedOperand) (v : Nat)
    (read : lowerOperandRead f ρ t.2 = some (some v)) :
    denotes f ρ m c (t :: terms) ↔ denotes f ρ m (c + t.1 * (v : Int)) terms := by
  rw [denotesCons]
  constructor
  · rintro ⟨w,_,earlier,rest⟩
    have same : w = v := Option.some.inj (Option.some.inj (earlier.symm.trans read))
    subst w
    exact rest
  · intro rest
    exact ⟨v,(hitRead f ρ t.2 v).mp read,read,rest⟩

private theorem sliceHit (f : Nat → Nat) (rank a : Nat) (c : Int)
    (terms : List WeightedOperand) (b : Int) (rest : List WeightedOperand)
    (within : slice f rank a c terms = some (some (b,rest))) :
    rest = untouched rank terms ∧
    ∀ ρ : Nat → Nat, ρ rank = a →
      ∃ values : List Nat, orderedReads f ρ (selected rank terms) values ∧
        b = c + actualSum (selected rank terms) values ∧
        ∀ (extra : Int) (m : Nat),
          (denotes f ρ m (c+extra) terms ↔ denotes f ρ m (b+extra) rest) := by
  induction terms generalizing b rest with
  | nil =>
    have equal : (c,([] : List WeightedOperand)) = (b,rest) :=
      Option.some.inj (Option.some.inj within)
    rcases Prod.mk.inj equal with ⟨same,empty⟩
    subst b
    subst rest
    exact ⟨rfl,fun _ _ => ⟨[],True.intro,by simp [selected,actualSum],fun _ _ => Iff.rfl⟩⟩
  | cons t ts ih =>
    change step t (expectedRead f rank a (1,t.2)) (slice f rank a c ts) =
      some (some (b,rest)) at within
    by_cases atRank : t.2.rank = rank
    · rw [expectedSelected f rank a t atRank] at within
      cases read : lowerOperandRead f (fun _ => a) t.2 with
      | none => simp [read,step] at within
      | some result =>
        cases result with
        | none => simp [read,step] at within
        | some v =>
          have paid : step t (some (some [(1,v)])) (slice f rank a c ts) =
              some (some (b,rest)) := by
            simpa only [read,Option.map_some] using within
          obtain ⟨⟨prior,more⟩,subSlice,operation⟩ := tailHit t [(1,v)] _ _ paid
          have equal : (prior + t.1 * (v : Int),more) = (b,rest) :=
            Option.some.inj (Option.some.inj operation)
          rcases Prod.mk.inj equal with ⟨newConst,newTerms⟩
          subst b
          subst rest
          obtain ⟨remain,hypothesis⟩ := ih prior more subSlice
          refine ⟨by simpa [untouched,atRank] using remain,?_⟩
          intro ρ agree
          obtain ⟨vs,reads,constant,meaning⟩ := hypothesis ρ agree
          have actualRead := (sameCoordinateRead f ρ rank a t.2 atRank agree).trans read
          have actual := (hitRead f ρ t.2 v).mp actualRead
          have picked : selected rank (t :: ts) = t :: selected rank ts := by simp [selected,atRank]
          refine ⟨v :: vs,?_,?_,?_⟩
          · rw [picked]
            exact ⟨actual,actualRead,reads⟩
          · rw [picked]
            change prior + t.1 * (v : Int) =
              c + (t.1 * (v : Int) + actualSum (selected rank ts) vs)
            rw [constant]
            ac_rfl
          · intro extra m
            have pay := denotesPaid f ρ m (c+extra) t ts v actualRead
            have shift := meaning (extra + t.1*(v : Int)) m
            have left : c + (extra + t.1*(v : Int)) = c + extra + t.1*(v : Int) := by ac_rfl
            have right : prior + (extra + t.1*(v : Int)) = prior + t.1*(v : Int) + extra := by ac_rfl
            rw [left,right] at shift
            exact pay.trans shift
    · rw [expectedUntouched f rank a t atRank] at within
      obtain ⟨⟨prior,more⟩,subSlice,operation⟩ := tailHit t [] _ _ within
      have equal : (prior,t :: more) = (b,rest) := Option.some.inj (Option.some.inj operation)
      rcases Prod.mk.inj equal with ⟨sameConst,sameTerms⟩
      subst b
      subst rest
      obtain ⟨remain,hypothesis⟩ := ih prior more subSlice
      refine ⟨by simp [untouched,atRank,remain],?_⟩
      intro ρ agree
      obtain ⟨vs,reads,constant,meaning⟩ := hypothesis ρ agree
      refine ⟨vs,by simpa [selected,atRank] using reads,by simpa [selected,atRank] using constant,?_⟩
      intro extra m
      rw [denotesCons,denotesCons]
      constructor
      · rintro ⟨v,actual,read,residual⟩
        have transfer := meaning (extra + t.1 * (v : Int)) m
        refine ⟨v,actual,read,?_⟩
        simpa only [add_assoc] using transfer.mp (by simpa only [add_assoc] using residual)
      · rintro ⟨v,actual,read,residual⟩
        have transfer := meaning (extra + t.1 * (v : Int)) m
        refine ⟨v,actual,read,?_⟩
        simpa only [add_assoc] using transfer.mpr (by simpa only [add_assoc] using residual)

theorem hitExact : HitExact := by
  intro f rank a c terms b rest within
  obtain ⟨untouched,hypothesis⟩ := sliceHit f rank a c terms b rest within
  refine ⟨untouched,?_⟩
  intro ρ agree
  obtain ⟨values,reads,constant,meaning⟩ := hypothesis ρ agree
  exact ⟨values,reads,constant,fun m _ => by simpa only [add_zero] using meaning 0 m⟩

end LogicLineages.PermittedControl.SignedRowCoordinateSlice
