module

public import LogicLineages.NativeModule.PersistentMarking.MarkedBaseTupleTargets
public import LogicLineages.NativeModule.PersistentMarking.HereditaryTupleProof
public import LogicLineages.NativeModule.PersistentMarking.HereditaryConstructionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedBaseTupleFoundationProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics MarkedBaseTuples

theorem enumeration : MarkedBaseTupleTargets.TupleEnumeration := by
  intro E Γ ds
  induction ds with
  | nil =>
    intro vs
    constructor
    · intro h; simp only [tuples,List.mem_cons,List.not_mem_nil,or_false] at h
      subst vs; exact HereditaryTupleProof.tupleNil E Γ
    · intro h
      have hl := h.1
      cases vs with
      | nil => exact List.mem_cons_self
      | cons v vs => simp at hl
  | cons σ ds ih =>
    intro vs
    constructor
    · intro h
      obtain ⟨c,hc,hs⟩ := List.mem_flatMap.mp h
      obtain ⟨cs,hcs,rfl⟩ := List.mem_map.mp hs
      exact (HereditaryTupleProof.tupleCons E Γ σ ds c cs).mpr ⟨hc,(ih cs).mp hcs⟩
    · intro h
      cases vs with
      | nil => have hl := h.1; simp at hl
      | cons c cs =>
        obtain ⟨hc,hcs⟩ := (HereditaryTupleProof.tupleCons E Γ σ ds c cs).mp h
        exact List.mem_flatMap.mpr ⟨c,hc,List.mem_map.mpr ⟨cs,(ih cs).mpr hcs,rfl⟩⟩

theorem distinct : MarkedBaseTupleTargets.TupleDistinct := by
  intro E Γ ds
  induction ds with
  | nil => exact .cons (by simp) .nil
  | cons σ ds ih =>
    apply List.pairwise_flatMap.mpr
    constructor
    · intro c hc
      exact ih.map (c::·) (fun a b hab he => hab (List.cons.inj he).2)
    · apply (HereditaryConstructionProof.distinct E σ Γ).imp
      intro a b hab xs hx ys hy he
      obtain ⟨as,has,rfl⟩ := List.mem_map.mp hx
      obtain ⟨bs,hbs,rfl⟩ := List.mem_map.mp hy
      exact hab (List.cons.inj he).1

theorem valuesCons (E : Environment) (Γ : Context) (σ : Ty) (ds : List Ty) (x y : Code) (xs ys : List Code) :
    ValuesLE E Γ (σ::ds) (x::xs) (y::ys) ↔ (descriptor E σ).le Γ x y = true ∧ ValuesLE E Γ ds xs ys := by
  constructor
  · intro h
    exact ⟨h 0 σ x y rfl rfl rfl,fun i τ a b ht ha hb => h (i+1) τ a b ht ha hb⟩
  · rintro ⟨h,ht⟩ i τ a b hd ha hb
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hd ha hb
      cases hd; cases ha; cases hb; exact h
    | succ i => exact ht i τ a b hd ha hb

theorem orderExact : MarkedBaseTupleTargets.TupleOrderExact := by
  intro E Γ ds
  induction ds with
  | nil =>
    intro xs ys hx hy
    have hxl := hx.1; have hyl := hy.1
    cases xs with
    | cons x xs => simp at hxl
    | nil =>
      cases ys with
      | cons y ys => simp at hyl
      | nil =>
        constructor
        · intro _ i τ a b h; cases i <;> cases h
        · intro _; rfl
  | cons σ ds ih =>
    intro xs ys hx hy
    cases xs with
    | nil => have h := hx.1; simp at h
    | cons x xs =>
      cases ys with
      | nil => have h := hy.1; simp at h
      | cons y ys =>
        have hxt := ((HereditaryTupleProof.tupleCons E Γ σ ds x xs).mp hx).2
        have hyt := ((HereditaryTupleProof.tupleCons E Γ σ ds y ys).mp hy).2
        rw [valuesCons]
        simp only [MarkedBaseTuples.tupleLe,Bool.and_eq_true,ih xs ys hxt hyt]
end LogicLineages.PersistentMarking.MarkedBaseTupleFoundationProof
