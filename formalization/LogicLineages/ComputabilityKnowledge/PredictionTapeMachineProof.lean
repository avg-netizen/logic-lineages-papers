module

public import LogicLineages.ComputabilityKnowledge.PredictionTapeMachineTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeMachineProof
open Turing PredictionTapeMachine PredictionTapeMachineTargets

private theorem halted (k : Nat) (b : Bool) (t : Tape Symbol) :
    step k ⟨.done b, t⟩ = none := rfl

private theorem computation (n : Nat) :
    ∀ (k : Nat) (i : Fin (k + 1)), i.val = n →
    ∀ (xs : List Bool) (left : ListBlank Symbol), ∃ t : Tape Symbol,
      Run k ⟨.scan i, Tape.mk' left (ListBlank.mk (xs.map some))⟩
        ⟨.done (decide (xs.length < n)), t⟩ (min n xs.length + 1) ∧
      t.head = some (decide (xs.length < n)) ∧
      t.right = ListBlank.mk ((xs.drop (min n xs.length + 1)).map some) := by
  induction n with
  | zero =>
    intro k i hi xs left
    refine ⟨(Tape.mk' left (ListBlank.mk (xs.map some))).write (some false), ?_, rfl, ?_⟩
    · have hs : step k ⟨.scan i, Tape.mk' left (ListBlank.mk (xs.map some))⟩ =
          some ⟨.done false, (Tape.mk' left (ListBlank.mk (xs.map some))).write (some false)⟩ := by
        simp [step, TM0.step, machine, hi]
      simpa using Run.next hs (Run.refl _)
    · cases xs <;> simp [Tape.write, Tape.mk']
  | succ n ih =>
    intro k i hi xs left
    have hne : i.val ≠ 0 := by omega
    cases xs with
    | nil =>
      refine ⟨(Tape.mk' left (ListBlank.mk [])).write (some true), ?_, rfl, ?_⟩
      · have hs : step k ⟨.scan i, Tape.mk' left (ListBlank.mk [])⟩ =
            some ⟨.done true, (Tape.mk' left (ListBlank.mk [])).write (some true)⟩ := by
          simp [step, TM0.step, machine, hne, Tape.mk', Symbol, default]
        simpa using Run.next hs (Run.refl _)
      · simp [Tape.write, Tape.mk']
    | cons a xs =>
      let j : Fin (k + 1) := ⟨i.val - 1, (Nat.sub_le i.val 1).trans_lt i.isLt⟩
      have hj : j.val = n := by simp [j, hi]
      obtain ⟨t, hr, hh, ht⟩ := ih k j hj xs (left.cons (some a))
      refine ⟨t, ?_, ?_, ?_⟩
      · have hs : step k ⟨.scan i, Tape.mk' left (ListBlank.mk ((a :: xs).map some))⟩ =
            some ⟨.scan j, Tape.mk' (left.cons (some a)) (ListBlank.mk (xs.map some))⟩ := by
          simp [step, TM0.step, machine, hne, Tape.move_right_mk', j]
        simpa using Run.next hs hr
      · simpa using hh
      · simpa using ht

private theorem initial_computation (k : Nat) (xs : List Bool) :
    ∃ t : Tape Symbol,
      Run k (initial k xs) ⟨.done (decide (xs.length < k)), t⟩ (min k xs.length + 1) ∧
      t.head = some (decide (xs.length < k)) ∧
      t.right = ListBlank.mk ((xs.drop (min k xs.length + 1)).map some) :=
  computation k k ⟨k, Nat.lt_succ_self k⟩ rfl xs (ListBlank.mk [])

theorem exactTapeComputation : ExactTapeComputation := by
  intro k xs
  obtain ⟨t, hr, hh, _⟩ := initial_computation k xs
  exact ⟨_, _, hr, halted k _ t, rfl, hh, by omega⟩

private theorem unique_run {k : Nat} {c d : Cfg k} {n : Nat} (h : Run k c d n) :
    ∀ (e : Cfg k) (m : Nat), step k d = none → Run k c e m → step k e = none →
      n = m ∧ d = e := by
  induction h with
  | refl c =>
    intro e m hc h' he
    cases h' with
    | refl => exact ⟨rfl, rfl⟩
    | next hs _ => simp [hc] at hs
  | @next c c' d n hs hr ih =>
    intro e m hd h' he
    cases h' with
    | refl => simp [he] at hs
    | @next _ c'' _ m hs' hr' =>
      have eq : c' = c'' := Option.some.inj (hs.symm.trans hs')
      subst c''
      obtain ⟨hn, hd⟩ := ih e m hd hr' he
      exact ⟨congrArg (· + 1) hn, hd⟩

theorem uniqueTapeComputation : UniqueTapeComputation := by
  intro k xs bit time h
  obtain ⟨d, n, hr, hd, hq, hh, ht⟩ := h
  obtain ⟨t, he, _, _⟩ := initial_computation k xs
  obtain ⟨hn, eq⟩ := unique_run hr _ _ hd he (halted k _ t)
  have hb : bit = decide (xs.length < k) := by
    have hstates := congrArg (fun c : Cfg k => c.q) eq
    rw [hq] at hstates
    exact State.done.inj hstates
  exact ⟨hb, by omega⟩

theorem unreadSuffixPreserved : UnreadSuffixPreserved := by
  intro k xs
  obtain ⟨t, hr, _, ht⟩ := initial_computation k xs
  exact ⟨_, hr, halted k _ t, ht⟩

theorem constantTapeRuntime : ConstantTapeRuntime := by
  intro k n
  refine ⟨?_, Nat.add_le_add_right (Nat.min_le_left k n) 2⟩
  intro xs hx
  simpa [hx] using exactTapeComputation k xs

end LogicLineages.ComputabilityKnowledge.PredictionTapeMachineProof
