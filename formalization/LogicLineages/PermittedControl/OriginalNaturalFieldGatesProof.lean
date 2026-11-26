module
public import LogicLineages.PermittedControl.OriginalNaturalFieldGatesTargets
import LogicLineages.PermittedControl.OriginalNaturalFieldGatesIdentityProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNaturalFieldGates
open OrdinalComparison FieldComparison

private theorem threeWayOf (R : ClosedNaturalFieldResult) (D : Prop) (V : Nat → Prop)
    (invalid : R = none ↔ ¬D)
    (actual : D → (∀ v, R = some (some v) ↔ V v) ∧ (R = some none ↔ ∀ v, ¬ V v)) :
    ThreeWay R D V := by
  refine ⟨invalid,?_,?_⟩
  · by_cases hd : D
    · exact (actual hd).2.trans ⟨fun h => ⟨hd,h⟩,fun h => h.2⟩
    · simp [invalid.mpr hd,hd]
  · intro v
    by_cases hd : D
    · exact ((actual hd).1 v).trans ⟨fun h => ⟨hd,h⟩,fun h => h.2⟩
    · simp [invalid.mpr hd,hd]

private theorem identityReadExact (mu : NONote) (x y : Nat) (V : Nat → Prop)
    (value : IdentityDomain mu x → ∀ v, V v ↔ v = y) :
    ThreeWay (identityRead mu x y) (IdentityDomain mu x) V := by
  by_cases hd : IdentityDomain mu x
  · have impossible : ¬ ∀ v, ¬ V v := fun all => all y ((value hd y).mpr rfl)
    refine ⟨?_,?_,?_⟩
    · simp [identityRead,hd]
    · simp [identityRead,hd,impossible]
    · intro v
      rw [identityRead,if_pos hd]
      constructor
      · intro h
        have eq : y = v := Option.some.inj (Option.some.inj h)
        exact ⟨hd,(value hd v).mpr eq.symm⟩
      · rintro ⟨_,vRead⟩
        rw [(value hd v).mp vRead]
  · have no : identityRead mu x y = none := by simp [identityRead,hd]
    refine ⟨?_,?_,?_⟩
    · simp [no,hd]
    · simp [no,hd]
    · intro v
      simp [no,hd]

theorem exactOrdinaryGateReads : ExactOrdinaryGateReads := by
  intro f g x
  cases g with
  | iterate k s o =>
      have actual := closedOrdinaryValueActual f (.iterate k) x
      exact threeWayOf _ _ _ actual.1 actual.2
  | entry P s o =>
      cases P with
      | proper lam mu =>
          have actual := closedOrdinaryValueActual f (.entry 0 lam mu) x
          have routed := threeWayOf _ _ _ actual.1 actual.2
          have sameValue (v : Nat) : FieldValue f (.entry 0 lam mu) x v ↔
              (Gate.entry (.proper lam mu) s o).value f x v := by
            simp only [Gate.value,Interval.firstHit,Interval.entryNorm,Interval.left,Interval.right,
              FieldValue,Function.iterate_zero,id_eq]
          refine ⟨routed.1,?_,?_⟩
          · exact routed.2.1.trans (and_congr Iff.rfl (forall_congr' fun v => not_congr (sameValue v)))
          · intro v
            exact (routed.2.2 v).trans (and_congr Iff.rfl (sameValue v))
      | identity mu =>
          exact identityReadExact mu x x _ (fun hd v => identityValue f mu x v hd)
  | count P s o =>
      cases P with
      | proper lam mu =>
          have actual := closedOrdinaryCountActual f lam mu x
          exact threeWayOf _ _ _ actual.1 actual.2
      | identity mu =>
          exact identityReadExact mu x 0 _ (fun hd v => identityHit f mu x v hd)

theorem exactOrdinarySharedGateGraph : ExactOrdinarySharedGateGraph := by
  intro f g ν θ
  refine ⟨(exactOrdinaryGateReads f g (θ g.source)).2.2 (θ g.output),?_⟩
  intro agrees
  have same : θ g.source = ν g.source := agrees _ List.mem_cons_self
  refine ⟨congrArg (fun x => g.readAt f x) same,?_⟩
  intro output
  unfold Gate.graph
  rw [same,output]

end LogicLineages.PermittedControl.OriginalNaturalFieldGates
