import LogicLineages.PersistentMarking.HereditaryNaturalityBridgeTargets
import LogicLineages.PersistentMarking.HereditaryPrefixCodingProof
namespace LogicLineages.PersistentMarking.HereditaryTupleOrderProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics

theorem valuesCons (E : Environment) (Δ : Context) (ρ : Ty) (ds : List Ty) (x y : Code) (xs ys : List Code) :
    ValuesLE E Δ (ρ::ds) (x::xs) (y::ys) ↔
      (descriptor E ρ).le Δ x y = true ∧ ValuesLE E Δ ds xs ys := by
  constructor
  · intro h
    exact ⟨h 0 ρ x y rfl rfl rfl,fun i τ a b hd hx hy => h (i+1) τ a b hd hx hy⟩
  · rintro ⟨h,hr⟩ i τ a b hd hx hy
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hd hx hy
      cases hd; cases hx; cases hy; exact h
    | succ i => exact hr i τ a b hd hx hy

theorem allExact (E : Environment) (Δ : Context) (ds : List Ty) (xs ys : List Code)
    (hx : ds.length = xs.length) (hy : ds.length = ys.length) :
    (ds.zip (xs.zip ys)).all (fun p => (descriptor E p.1).le Δ p.2.1 p.2.2) = true ↔
      ValuesLE E Δ ds xs ys := by
  induction ds generalizing xs ys with
  | nil =>
    cases xs with
    | cons x xs => cases hx
    | nil =>
      cases ys with
      | cons y ys => cases hy
      | nil =>
        constructor
        · intro _ i τ a b hd; cases i <;> cases hd
        · intro _; rfl
  | cons ρ ds ih =>
    cases xs with
    | nil => cases hx
    | cons x xs =>
      cases ys with
      | nil => cases hy
      | cons y ys =>
        rw [valuesCons]
        simp only [List.zip_cons_cons,List.all_cons,Bool.and_eq_true]
        exact and_congr Iff.rfl (ih xs ys (Nat.succ.inj hx) (Nat.succ.inj hy))

theorem attachedAll (ds : List Ty) (pairs : List (Code × Code)) (f : Ty × (Code × Code) → Bool) :
    (ds.attach.zip pairs).all (fun p => f (p.1.val,p.2)) = (ds.zip pairs).all f := by
  have h : (ds.attach.zip pairs).map (Prod.map Subtype.val id) = ds.zip pairs := by
    rw [← List.zip_map_left,List.attach_map_subtype_val]
  rw [← h,List.all_map]
  rfl

theorem exactOrder : HereditaryNaturalityBridgeTargets.TupleLeExact := by
  intro E σ Δ p xs ys vs ws hx hy
  have hv := hx
  have hw := hy
  rw [HereditaryTupleAdapterProof.tupleDecodeCanonical] at hv hw
  have hvl := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 xs vs hv).1.1
  have hwl := (HereditaryTupleRoundtripProof.indicesAfterValues E Δ p.val.1 ys ws hw).1.1
  unfold tupleLe
  rw [hx,hy]
  change (p.val.1.attach.zip (vs.zip ws)).all
    (fun q => (descriptor E q.1.val).le Δ q.2.1 q.2.2) = true ↔ _
  rw [attachedAll p.val.1 (vs.zip ws) (fun q => (descriptor E q.1).le Δ q.2.1 q.2.2)]
  exact allExact E Δ p.val.1 vs ws hvl hwl

end LogicLineages.PersistentMarking.HereditaryTupleOrderProof
