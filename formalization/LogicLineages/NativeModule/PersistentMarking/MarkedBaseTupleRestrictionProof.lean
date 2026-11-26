module

public import LogicLineages.NativeModule.PersistentMarking.MarkedBaseTupleFoundationProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedExtrasRestrictionProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryRestrictionAlgebraProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedBaseTupleRestrictionProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedBaseTuples

theorem restriction : MarkedBaseTupleTargets.TupleRestriction := by
  intro E Γ Θ ds xs hw ht he hx
  induction ds generalizing xs with
  | nil =>
    cases xs with
    | nil => exact HereditaryTupleProof.tupleNil E Θ
    | cons x xs => cases hx.1
  | cons σ ds ih =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have hp := (HereditaryTupleProof.tupleCons E Γ σ ds x xs).mp hx
      apply (HereditaryTupleProof.tupleCons E Θ σ ds _ _).mpr
      exact ⟨(HereditaryRestrictionProof.restriction E σ Γ Θ hw ht he x hp.1).1,ih xs hp.2⟩

theorem monotone : MarkedBaseTupleTargets.TupleRestrictionMonotone := by
  intro E Γ Θ ds xs ys hw ht he hx hy hxy
  induction ds generalizing xs ys with
  | nil =>
    cases xs with
    | cons x xs => cases hx.1
    | nil =>
      cases ys with
      | cons y ys => cases hy.1
      | nil => rfl
  | cons σ ds ih =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      cases ys with
      | nil => cases hy.1
      | cons y ys =>
        have hp := (HereditaryTupleProof.tupleCons E Γ σ ds x xs).mp hx
        have hq := (HereditaryTupleProof.tupleCons E Γ σ ds y ys).mp hy
        change ((descriptor E σ).le Γ x y && tupleLe E Γ ds xs ys) = true at hxy
        simp only [Bool.and_eq_true] at hxy
        change ((descriptor E σ).le Θ ((descriptor E σ).restrict Γ Θ x) ((descriptor E σ).restrict Γ Θ y) &&
          tupleLe E Θ ds (restrictTuple E Γ Θ ds xs) (restrictTuple E Γ Θ ds ys)) = true
        simp only [Bool.and_eq_true]
        exact ⟨MarkedExtrasRestrictionProof.codeMonotone E σ Γ Θ hw ht he x y hp.1 hq.1 hxy.1,
          ih xs ys hp.2 hq.2 hxy.2⟩

theorem identity (E : Environment) (Γ : Context) (ds : List Ty) (xs : List Code)
    (hw : WellFormed E.types E.ports Γ) (hx : TupleValues E Γ ds xs) : restrictTuple E Γ Γ ds xs = xs := by
  induction ds generalizing xs with
  | nil => cases xs with
    | nil => rfl
    | cons x xs => cases hx.1
  | cons σ ds ih =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have hp := (HereditaryTupleProof.tupleCons E Γ σ ds x xs).mp hx
      change (descriptor E σ).restrict Γ Γ x :: restrictTuple E Γ Γ ds xs = x::xs
      rw [(HereditaryRestrictionAlgebraProof.algebra E σ).1 Γ x hw hp.1,ih xs hp.2]

theorem composition (E : Environment) (Γ Δ Θ : Context) (ds : List Ty) (xs : List Code)
    (hw : WellFormed E.types E.ports Γ) (hd : WellFormed E.types E.ports Δ)
    (ht : WellFormed E.types E.ports Θ) (he : Extends Γ Δ) (hf : Extends Δ Θ)
    (hx : TupleValues E Γ ds xs) :
    restrictTuple E Δ Θ ds (restrictTuple E Γ Δ ds xs) = restrictTuple E Γ Θ ds xs := by
  induction ds generalizing xs with
  | nil => cases xs with
    | nil => rfl
    | cons x xs => cases hx.1
  | cons σ ds ih =>
    cases xs with
    | nil => cases hx.1
    | cons x xs =>
      have hp := (HereditaryTupleProof.tupleCons E Γ σ ds x xs).mp hx
      change (descriptor E σ).restrict Δ Θ ((descriptor E σ).restrict Γ Δ x) ::
        restrictTuple E Δ Θ ds (restrictTuple E Γ Δ ds xs) =
        (descriptor E σ).restrict Γ Θ x :: restrictTuple E Γ Θ ds xs
      rw [(HereditaryRestrictionAlgebraProof.algebra E σ).2 Γ Δ Θ x hw hd ht he hf hp.1,ih xs hp.2]

theorem algebra : MarkedBaseTupleTargets.TupleRestrictionAlgebra := by
  intro E ds
  exact ⟨fun Γ xs hw hx => identity E Γ ds xs hw hx,
    fun Γ Δ Θ xs hw hd ht he hf hx => composition E Γ Δ Θ ds xs hw hd ht he hf hx⟩
end LogicLineages.PersistentMarking.MarkedBaseTupleRestrictionProof
