module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphLayoutProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphShiftProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison

private theorem andFold (xs : List Bool) : xs.foldr (· && ·) true = true ↔ ∀ b ∈ xs, b=true := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp only [List.foldr_cons,Bool.and_eq_true,ih,List.forall_mem_cons]

private theorem orFold (xs : List Bool) (r : Bool) : xs.foldr (· || ·) r=true ↔
    (∃ b∈xs, b=true) ∨ r=true := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldr_cons,Bool.or_eq_true,ih]
    simp only [List.mem_cons,exists_eq_or_imp]
    tauto

/-- Each finite numerical gate uses an actual f(k) for k<4 or the exact S
call f(x+4). The high-branch side constraint is separate and local. -/
def GateSpec (f : Nat→Nat) (u v arg : Nat) : Prop :=
  (∃ j : Nat, j<4 ∧ u=j ∧ v=f j) ∨ (u=arg+4 ∧ v=f (arg+4))

theorem gateSemantics (f w : Nat→Nat) (a b x : Nat) :
    fGate (evalLayout f w) (smallValues f) a b x=true ↔ GateSpec f (w a) (w b) (w x) := by
  unfold fGate GateSpec
  change ((List.range 4).map (fun j => decide (w a=j) &&
      decide (w b=(smallValues f).getD j 0))).foldr (· || ·)
      (decide (w a=w x+4) && decide (w b=f (w x+4))) = true ↔ _
  rw [orFold]
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.mem_map]
  constructor
  · rintro (⟨b,⟨j,hj,rfl⟩,e,l⟩|h)
    · have hj' := List.mem_range.mp hj
      have hget : (smallValues f).getD j 0=f j := by
        simp [smallValues,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hj']
      exact Or.inl ⟨j,hj',e,l.trans hget⟩
    · exact Or.inr h
  · rintro (⟨j,hj,e,l⟩|h)
    · have hget : (smallValues f).getD j 0=f j := by
        simp [smallValues,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hj]
      exact Or.inl ⟨(decide (w a=j) && decide (w b=(smallValues f).getD j 0)),
        ⟨j,List.mem_range.mpr hj,rfl⟩,e,l.trans hget.symm⟩
    · exact Or.inr h

theorem gateFunctional (f : Nat→Nat) {u v a : Nat} (h : GateSpec f u v a) : v=f u := by
  rcases h with ⟨j,_,rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl

theorem gateWitness (f : Nat→Nat) (u : Nat) : GateSpec f u (f u) (u-4) := by
  by_cases h : u<4
  · exact Or.inl ⟨u,h,rfl,rfl⟩
  · have he : u=u-4+4 := by omega
    exact Or.inr ⟨he,congrArg f he⟩

theorem prefixNumerical (f w : Nat→Nat) (t y n : Nat) (xs : List Nat) :
    prefixBody (evalLayout f w) t y n xs=true ↔
      ∃ k : Nat, k<xs.length ∧ w t=n+k ∧ w y=xs.getD k 0 := by
  induction xs generalizing n with
  | nil => simp [prefixBody,evalLayout]
  | cons x xs ih =>
    simp only [prefixBody,evalLayout,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq]
    change (w t=n ∧ w y=x) ∨ prefixBody (evalLayout f w) t y (n+1) xs=true ↔ _
    rw [ih]
    constructor
    · rintro (⟨ht,hy⟩|⟨k,hk,ht,hy⟩)
      · exact ⟨0,by simp,by simpa,hy⟩
      · exact ⟨k+1,by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hk,
          by omega,by simpa only [List.getD_cons_succ] using hy⟩
    · rintro ⟨k,hk,ht,hy⟩
      cases k with
      | zero => exact Or.inl ⟨by simpa using ht,hy⟩
      | succ k =>
        have h : k<xs.length := by simpa only [List.length_cons,Nat.add_lt_add_iff_right] using hk
        exact Or.inr ⟨k,h,by omega,by simpa only [List.getD_cons_succ] using hy⟩

theorem exactPointValue (f : Nat→Nat) (ξ : Ordinal) (base k : Nat)
    (hk : k<(max (actualOrdinalNorm ξ) base - actualOrdinalNorm ξ)) :
    (exactPoints f ξ base).getD k 0 = J f ξ (actualOrdinalNorm ξ+k) := by
  simp [exactPoints,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,hk]

theorem exactPointLength (f : Nat→Nat) (ξ : Ordinal) (base : Nat) :
    (exactPoints f ξ base).length=max (actualOrdinalNorm ξ) base-actualOrdinalNorm ξ := by simp [exactPoints]

/-- Record of the exact branch-local numerical conditions, with the ray
formula evaluated at the actual relocated witnesses. -/
def TailSpec (f w : Nat→Nat) (wr δ nξ base : Nat) (ray : Bool) : Prop :=
  let t := directWidth wr δ
  let u := uSlot wr
  max nξ base ≤ w t ∧ w (u 0)=w t ∧ w (wr+2)=0 ∧
    w (u δ)=base+w (wr+1) ∧ ray=true ∧ w (t+1)=w wr+(δ+1) ∧
    ∀ j<δ, GateSpec f (w (u j)) (w (u (j+1))) (w (argSlot wr δ j))

theorem tailNumerical (f w : Nat→Nat) (wr δ nξ base : Nat) (ray : Bool) :
    tailBody (evalLayout f w) wr δ nξ base (smallValues f) ray=true ↔ TailSpec f w wr δ nξ base ray := by
  unfold tailBody TailSpec
  change (([decide (max nξ base≤w (directWidth wr δ)),decide (w (uSlot wr 0)=w (directWidth wr δ)),
    decide (w (wr+2)=0),decide (w (uSlot wr δ)=base+w (wr+1)),ray,
    decide (w (directWidth wr δ+1)=w wr+(δ+1))] ++
    (List.range δ).map (fun j => fGate (evalLayout f w) (smallValues f) (uSlot wr j)
      (uSlot wr (j+1)) (argSlot wr δ j))).foldr (· && ·) true) = true ↔ _
  rw [andFold]
  simp only [List.mem_append,forall_or_left,List.forall_mem_cons,decide_eq_true_eq,List.not_mem_nil,
    false_implies,implies_true,and_true,List.forall_mem_map,List.mem_range,gateSemantics]

private theorem iterateStep (f : Nat→Nat) (n t : Nat) : (f^[n+1]) t=f ((f^[n]) t) := by
  rw [Function.iterate_succ_apply']

theorem iterateLower (f : Nat→Nat) (hf : ∀ n, n≤f n) (δ t : Nat) : t≤(f^[δ]) t := by
  induction δ with
  | zero => exact le_rfl
  | succ n ih => rw [iterateStep]; exact ih.trans (hf _)

theorem tailChain (f w : Nat→Nat) (wr δ nξ base : Nat) (ray : Bool)
    (h : TailSpec f w wr δ nξ base ray) : w (uSlot wr δ)=(f^[δ]) (w (directWidth wr δ)) := by
  have H (n : Nat) (hn : n≤δ) : w (uSlot wr n)=(f^[n]) (w (directWidth wr δ)) := by
    induction n with
    | zero => exact h.2.1
    | succ n ih =>
      have hn' : n<δ := by omega
      rw [iterateStep,← ih (by omega)]
      exact gateFunctional f (h.2.2.2.2.2.2 n hn')
  exact H δ le_rfl

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
