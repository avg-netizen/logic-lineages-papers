module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsValueProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsGraph

abbrev Input := List Nat × Nat
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem computable_ite {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} [DecidablePred p] {f g : A → B}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  apply (Computable.cond hp hf hg).of_eq
  intro a
  by_cases h : p a <;> simp [h]

def termChildren (p : Input) : List Input :=
  if p.2 % 4 = 2 then [(p.1, (p.2 / 4).unpair.1), (p.1, (p.2 / 4).unpair.2)] else []

def formulaChildren (extend : Bool) (p : Input) : List Input :=
  if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then []
  else if p.2 % 5 = 2 then [(p.1, p.2 / 5)]
  else if p.2 % 5 = 3 then [(p.1, (p.2 / 5).unpair.1), (p.1, (p.2 / 5).unpair.2)]
  else [(if extend then (p.2 / 5).unpair.1 :: p.1 else p.1, (p.2 / 5).unpair.2)]

theorem termChildren_decreasing : ∀ p q, q ∈ termChildren p → q.2 < p.2 := by
  intro p q h
  by_cases ht : p.2 % 4 = 2
  · have hp : 0 < p.2 := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 4)
    have hl := Nat.unpair_left_le (p.2 / 4)
    have hr := Nat.unpair_right_le (p.2 / 4)
    simp only [termChildren, if_pos ht, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> dsimp <;> omega
  · simp [termChildren, ht] at h

theorem formulaChildren_decreasing (extend : Bool) : ∀ p q, q ∈ formulaChildren extend p → q.2 < p.2 := by
  intro p q h
  by_cases hleaf : p.2 % 5 = 0 ∨ p.2 % 5 = 1
  · simp [formulaChildren, hleaf] at h
  have hp : 0 < p.2 := by omega
  have hd := Nat.div_lt_self hp (by decide : 1 < 5)
  have hl := Nat.unpair_left_le (p.2 / 5)
  have hr := Nat.unpair_right_le (p.2 / 5)
  unfold formulaChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals first | subst q | (rcases h with rfl | rfl)
  all_goals omega

theorem tag_primitive (k : Nat) : Primrec (fun p : Input => p.2 % k) :=
  Primrec.nat_mod.comp Primrec.snd (Primrec.const k)
theorem quotient_primitive (k : Nat) : Primrec (fun p : Input => p.2 / k) :=
  Primrec.nat_div.comp Primrec.snd (Primrec.const k)
theorem tag_is (k n : Nat) : PrimrecPred (fun p : Input => p.2 % k = n) :=
  Primrec.eq.comp (tag_primitive k) (Primrec.const n)
theorem left_primitive (k : Nat) : Primrec (fun p : Input => (p.2 / k).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp (quotient_primitive k))
theorem right_primitive (k : Nat) : Primrec (fun p : Input => (p.2 / k).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp (quotient_primitive k))

theorem termChildren_primitive : Primrec termChildren :=
  Primrec.ite (tag_is 4 2)
    (Primrec.list_cons.comp (Primrec.fst.pair (left_primitive 4))
      (Primrec.list_cons.comp (Primrec.fst.pair (right_primitive 4)) (Primrec.const [])))
    (Primrec.const [])

theorem formulaChildren_primitive (extend : Bool) : Primrec (formulaChildren extend) := by
  have hctx : Primrec (fun p : Input => if extend then (p.2 / 5).unpair.1 :: p.1 else p.1) := by
    cases extend
    · exact Primrec.fst
    · exact Primrec.list_cons.comp (left_primitive 5) Primrec.fst
  exact Primrec.ite ((tag_is 5 0).or (tag_is 5 1)) (Primrec.const [])
    (Primrec.ite (tag_is 5 2)
      (Primrec.list_cons.comp (Primrec.fst.pair (quotient_primitive 5)) (Primrec.const []))
      (Primrec.ite (tag_is 5 3)
        (Primrec.list_cons.comp (Primrec.fst.pair (left_primitive 5))
          (Primrec.list_cons.comp (Primrec.fst.pair (right_primitive 5)) (Primrec.const [])))
        (Primrec.list_cons.comp (hctx.pair (right_primitive 5)) (Primrec.const []))))

theorem avoids_primitive : Primrec₂ (fun (vars bound : List Nat) => vars.all (fun i => !bound.contains i)) := by
  have hm : PrimrecRel (fun (xs : List Nat) (i : Nat) => ∃ j ∈ xs, j = i) :=
    (show PrimrecRel (fun a b : Nat => a = b) from Primrec.eq).exists_mem_list
  have hn : PrimrecRel (fun (xs : List Nat) (i : Nat) => i ∉ xs) := hm.not.of_eq (by intros; simp)
  have hs : PrimrecRel (fun (i : Nat) (xs : List Nat) => i ∉ xs) := hn.comp Primrec.snd Primrec.fst
  have ha : PrimrecRel (fun (vars bound : List Nat) => ∀ i ∈ vars, i ∉ bound) :=
    PrimrecRel.forall_mem_list hs
  apply ha.decide.of_eq
  intro vars bound
  apply Bool.eq_iff_iff.mpr
  simp

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ScopedPhiProgramsGraph
