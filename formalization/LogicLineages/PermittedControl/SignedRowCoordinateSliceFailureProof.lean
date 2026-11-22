module
public import LogicLineages.PermittedControl.SignedRowCoordinateSliceTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.SignedRowCoordinateSlice
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)

private def failureCondition (f : Nat → Nat) (a : Nat) (t : WeightedOperand) : Failure → Prop
  | .invalid => ¬ sourceDomain a t.2
  | .genuineMiss => sourceDomain a t.2 ∧ ∀ v, ¬ LowerOperandActual f (fun _ => a) t.2 v

private def failureResult (kind : Failure) : Result LowerOperand :=
  match kind with
  | .invalid => none
  | .genuineMiss => some none

private theorem firstFailureCons (f : Nat → Nat) (rank a : Nat) (t : WeightedOperand)
    (ts : List WeightedOperand) (kind : Failure) :
    firstFailure f rank a (t :: ts) kind ↔
      (t.2.rank = rank ∧ failureCondition f a t kind) ∨
      ((t.2.rank = rank → ∃ v, LowerOperandActual f (fun _ => a) t.2 v) ∧
        firstFailure f rank a ts kind) := by
  constructor
  · rintro ⟨earlier,bad,later,whole,atRank,reads,failed⟩
    cases earlier with
    | nil =>
      have same := (List.cons.inj whole).1
      subst bad
      exact Or.inl ⟨atRank,failed⟩
    | cons early rest =>
      have same := (List.cons.inj whole).1
      have suffix := (List.cons.inj whole).2
      subst early
      exact Or.inr ⟨reads t List.mem_cons_self,
        ⟨rest,bad,later,suffix,atRank,fun u hu => reads u (List.mem_cons_of_mem _ hu),failed⟩⟩
  · rintro (⟨atRank,failed⟩ | ⟨head,⟨earlier,bad,later,whole,atRank,reads,failed⟩⟩)
    · exact ⟨[],t,ts,rfl,atRank,by simp,failed⟩
    · refine ⟨t :: earlier,bad,later,congrArg (List.cons t) whole,atRank,?_,failed⟩
      intro u hu
      rcases List.mem_cons.mp hu with equal | before
      · subst u
        exact head
      · exact reads u before

private theorem propagateFailure (t : WeightedOperand) (hits : List (Nat × Nat))
    (tail : Result LowerOperand) (kind : Failure) :
    step t (some (some hits)) tail = failureResult kind ↔ tail = failureResult kind := by
  cases tail with
  | none => cases kind <;> simp [step,failureResult]
  | some content => cases content <;> cases kind <;> simp [step,failureResult]

private theorem failureAt (f : Nat → Nat) (rank a : Nat) (c : Int)
    (terms : List WeightedOperand) (kind : Failure) :
    slice f rank a c terms = failureResult kind ↔ firstFailure f rank a terms kind := by
  induction terms with
  | nil => cases kind <;> simp [slice,failureResult,firstFailure]
  | cons t ts ih =>
    change step t (FiniteStripCollectorRecovery.expectedRead f rank a (1,t.2))
      (slice f rank a c ts) = failureResult kind ↔ _
    rw [firstFailureCons]
    by_cases atRank : t.2.rank = rank
    · rw [expectedSelected f rank a t atRank]
      have spec := fixedReadFailures f a t.2
      cases result : lowerOperandRead f (fun _ => a) t.2 with
      | none =>
        have outside := spec.1.mp result
        have noValue : ¬ ∃ v, LowerOperandActual f (fun _ => a) t.2 v := by
          rintro ⟨v,hv⟩
          have read := (hitRead f (fun _ => a) t.2 v).mpr hv
          rw [result] at read
          cases read
        cases kind <;> simp [step,failureResult,failureCondition,atRank,outside,noValue]
      | some read =>
        cases read with
        | none =>
          obtain ⟨domain,noValue⟩ := spec.2.mp result
          have noHit : ¬ ∃ v, LowerOperandActual f (fun _ => a) t.2 v := by
            rintro ⟨v,hv⟩
            exact noValue v hv
          cases kind <;> simp [step,failureResult,failureCondition,atRank,domain,noValue,noHit]
        | some v =>
          have hit := (hitRead f (fun _ => a) t.2 v).mp result
          have existsHit : ∃ w, LowerOperandActual f (fun _ => a) t.2 w := ⟨v,hit⟩
          have inDomain : sourceDomain a t.2 := by
            by_contra outside
            have bad := spec.1.mpr outside
            rw [result] at bad
            cases bad
          have noMiss : ¬ (∀ w, ¬ LowerOperandActual f (fun _ => a) t.2 w) :=
            fun absent => absent v hit
          change step t (some (some [(1,v)])) (slice f rank a c ts) = failureResult kind ↔ _
          rw [propagateFailure,ih]
          cases kind <;> simp [failureCondition,atRank,inDomain,noMiss,existsHit]
    · rw [expectedUntouched f rank a t atRank,propagateFailure,ih]
      simp [atRank]

theorem failureExact : FailureExact := by
  intro f rank a c terms
  exact ⟨failureAt f rank a c terms .invalid, failureAt f rank a c terms .genuineMiss⟩

end LogicLineages.PermittedControl.SignedRowCoordinateSlice
