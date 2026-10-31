module
public import LogicLineages.ComputabilityKnowledge.PredictionTapeCodeTargets
public import LogicLineages.ComputabilityKnowledge.PredictionTapeTableProof
public import LogicLineages.ComputabilityKnowledge.PredictionTapeMachineProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapeCodeProof
open Turing PredictionTapeTable PredictionTapeCode PredictionTapeCodeTargets

private theorem pr_entry : Primrec (fun z : Nat × Nat => entry z.1 z.2) := by
  have hq : Primrec (fun z : Nat × Nat => z.2 / 3) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 3)
  have hm : Primrec (fun z : Nat × Nat => z.2 % 3) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 3)
  have hf : Primrec (fun z : Nat × Nat => some (z.1 + 1, (Sum.inr (some false) : Action))) :=
    Primrec.option_some.comp ((Primrec.nat_add.comp Primrec.fst (Primrec.const 1)).pair
      (Primrec.const (Sum.inr (some false) : Action)))
  have ht : Primrec (fun z : Nat × Nat => some (z.1 + 2, (Sum.inr (some true) : Action))) :=
    Primrec.option_some.comp ((Primrec.nat_add.comp Primrec.fst (Primrec.const 2)).pair
      (Primrec.const (Sum.inr (some true) : Action)))
  have hr : Primrec (fun z : Nat × Nat => some (z.2 / 3 - 1, (Sum.inl true : Action))) :=
    Primrec.option_some.comp ((Primrec.nat_sub.comp hq (Primrec.const 1)).pair
      (Primrec.const (Sum.inl true : Action)))
  exact Primrec.ite (Primrec.nat_le.comp hq Primrec.fst)
    (Primrec.ite (Primrec.eq.comp hq (Primrec.const 0)) hf
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) ht hr)) (Primrec.const none)

theorem effectiveCodeFamily : EffectiveCodeFamily := by
  have hl : Primrec (fun k : Nat => List.range ((k + 3) * 3)) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp
      (Primrec.nat_add.comp Primrec.id (Primrec.const 3)) (Primrec.const 3))
  exact Primrec.encode.comp (Primrec.id.pair (Primrec.list_map hl pr_entry.to₂))

private theorem lookup_entry (k q : Nat) (a : Symbol) (hq : q < k + 3) :
    lookup (table k) q a = entry k (q * 3 + symbolIndex a) := by
  have ha : symbolIndex a < 3 := by cases a with | none => decide | some b => cases b <;> decide
  have hi : q * 3 + symbolIndex a < (k + 3) * 3 := by omega
  simp [lookup, table, List.getElem?_eq_getElem, hi]

private theorem machine_agrees (k : Nat) (s : PredictionTapeMachine.State k) (a : Symbol) :
    machine (table k) (embedState k s) a =
      (PredictionTapeMachine.machine k s a).map (fun x => (embedState k x.1, x.2)) := by
  cases s with
  | scan i =>
    have hi : i.val ≤ k := by omega
    rw [show embedState k (.scan i) = i.val from rfl]
    unfold machine
    rw [lookup_entry k i.val a (by omega)]
    by_cases hz : i.val = 0 <;> cases a with
    | none => simp [entry, symbolIndex, PredictionTapeMachine.machine, embedState, hi, actionStmt, hz]
    | some b =>
      cases b <;>
        simp [entry, symbolIndex, PredictionTapeMachine.machine, embedState, hi, actionStmt, hz,
          Nat.add_div, Nat.add_mod]
  | done b =>
    cases b <;> unfold machine <;>
      rw [lookup_entry k _ a (by simp [embedState])] <;>
      cases a with
      | none => simp [entry, symbolIndex, embedState, PredictionTapeMachine.machine]
      | some b => cases b <;> simp [entry, symbolIndex, embedState,
          PredictionTapeMachine.machine, Nat.add_div, Nat.add_mod]

theorem exactCompiledStep : ExactCompiledStep := by
  intro k c
  rcases c with ⟨s, t⟩
  simp only [TM0.step, embedCfg, PredictionTapeMachine.step]
  rw [machine_agrees]
  cases h : PredictionTapeMachine.machine k s t.head with
  | none => rfl
  | some x => rcases x with ⟨s', a⟩; cases a <;> rfl

private theorem lifted_step (k : Nat) (c : PredictionTapeMachine.Cfg k) (r : Raw)
    (h : toCfg r = embedCfg k c) :
    (step (table k) r).map toCfg = (PredictionTapeMachine.step k c).map (embedCfg k) := by
  rw [PredictionTapeTableProof.exactSingleStep, h, exactCompiledStep]

private theorem lift_run {k : Nat} {c d : PredictionTapeMachine.Cfg k} {n : Nat}
    (h : PredictionTapeMachine.Run k c d n) :
    ∀ r : Raw, toCfg r = embedCfg k c →
      ∃ s : Raw, Run (table k) r s n ∧ toCfg s = embedCfg k d := by
  induction h with
  | refl c => intro r hr; exact ⟨r, Run.refl r, hr⟩
  | @next c c' d n hs hr ih =>
    intro r he
    have hm := lifted_step k c r he
    rw [hs] at hm
    cases ht : step (table k) r with
    | none => simp [ht] at hm
    | some r' =>
      have he' : toCfg r' = embedCfg k c' := Option.some.inj (by simpa [ht] using hm)
      obtain ⟨s, hs', hd⟩ := ih r' he'
      exact ⟨s, Run.next ht hs', hd⟩

private theorem base_run (k : Nat) (xs : List Bool) : ∃ r : Raw,
    Run (table k) (initial (table k) xs) r (min k xs.length + 1) ∧
    step (table k) r = none ∧
    r.1 = (if xs.length < k then k + 2 else k + 1) ∧
    r.2.1 = some (decide (xs.length < k)) := by
  obtain ⟨d, n, hr, hd, hq, hh, hn⟩ := PredictionTapeMachineProof.exactTapeComputation k xs
  have hlen : n = min k xs.length + 1 := by omega
  subst n
  obtain ⟨r, hrun, he⟩ := lift_run hr (initial (table k) xs) rfl
  have hm := lifted_step k d r he
  rw [hd] at hm
  have halt : step (table k) r = none := by
    cases ht : step (table k) r with
    | none => rfl
    | some s => simp [ht] at hm
  have hstate := congrArg (fun c : TM0.Cfg Symbol Nat => c.q) he
  have hhead := congrArg (fun c : TM0.Cfg Symbol Nat => c.Tape.head) he
  refine ⟨r, hrun, halt, ?_, ?_⟩
  · simpa [toCfg, embedCfg, hq, embedState] using hstate
  · simpa [toCfg, embedCfg, hh] using hhead

private theorem unique_run {p : Table} {c d : Raw} {n : Nat} (h : Run p c d n) :
    ∀ (e : Raw) (m : Nat), step p d = none → Run p c e m → step p e = none →
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

private theorem simulate_eq (k fuel : Nat) (xs : List Bool) :
    simulate (code k) fuel xs = bounded (table k) fuel (initial (table k) xs) := by
  simp [simulate, code, PredictionTapeTableProof.effectiveDecoding.2]

theorem exactCodedRuntime : ExactCodedRuntime := by
  intro k xs fuel
  obtain ⟨r, hr, hh, _, _⟩ := base_run k xs
  constructor
  · rintro ⟨d, hd⟩
    rw [simulate_eq] at hd
    obtain ⟨n, hn, hrun, hhalt⟩ := (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).1 hd
    have he := (unique_run hr d n hh hrun hhalt).1
    omega
  · intro h
    refine ⟨r, ?_⟩
    rw [simulate_eq]
    exact (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).2
      ⟨min k xs.length + 1, by omega, hr, hh⟩

theorem exactCodedOutput : ExactCodedOutput := by
  intro k xs fuel d hd
  obtain ⟨r, hr, hh, hq, hb⟩ := base_run k xs
  rw [simulate_eq] at hd
  obtain ⟨n, _, hrun, hhalt⟩ := (PredictionTapeTableProof.exactBoundedSimulation _ _ _ _).1 hd
  have he := (unique_run hr d n hh hrun hhalt).2
  subst d
  exact ⟨hq, hb⟩

theorem uniformConstantTime : UniformConstantTime := by
  intro k xs
  obtain ⟨d, hd⟩ := (exactCodedRuntime k xs (k + 2)).2 (by omega)
  exact ⟨d, hd, (exactCodedOutput k xs (k + 2) d hd).2⟩

end LogicLineages.ComputabilityKnowledge.PredictionTapeCodeProof
