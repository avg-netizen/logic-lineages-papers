module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetProof
open Turing PredictionFiniteAlphabet PredictionFiniteAlphabetTargets

theorem effectiveDecoding : EffectiveDecoding := by
  refine ⟨Primrec.option_getD.comp Primrec.decode (Primrec.const (0, 0, [])), ?_⟩
  intro p
  simp [decodeTable]

private theorem pr_width : Primrec width :=
  Primrec.nat_add.comp Primrec.fst (Primrec.const 3)

private theorem pr_lookup : Primrec (fun z : Table × Nat × Nat => lookup z.1 z.2.1 z.2.2) := by
  have hw := pr_width.comp (Primrec.fst : Primrec (fun z : Table × Nat × Nat => z.1))
  have hi : Primrec (fun z : Table × Nat × Nat => z.2.1 * width z.1 + z.2.2 % width z.1) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) hw)
      (Primrec.nat_mod.comp (Primrec.snd.comp Primrec.snd) hw)
  exact Primrec.option_bind
    (Primrec.list_getElem?.comp ((Primrec.snd.comp Primrec.snd).comp Primrec.fst) hi) Primrec.snd.to₂

private theorem pr_execute {α : Type} [Primcodable α]
    {q : α → Nat} {a : α → Action} {c : α → Raw}
    (hq : Primrec q) (ha : Primrec a) (hc : Primrec c) :
    Primrec (fun x => execute (q x) (a x) (c x)) := by
  have head := (Primrec.fst.comp Primrec.snd).comp hc
  have left := (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).comp hc
  have right := (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)).comp hc
  have hl : Primrec (fun x => (q x, (c x).2.2.1.headI, (c x).2.2.1.tail, (c x).2.1 :: (c x).2.2.2)) :=
    hq.pair ((Primrec.list_headI.comp left).pair
      ((Primrec.list_tail.comp left).pair (Primrec.list_cons.comp head right)))
  have hr : Primrec (fun x => (q x, (c x).2.2.2.headI, (c x).2.1 :: (c x).2.2.1, (c x).2.2.2.tail)) :=
    hq.pair ((Primrec.list_headI.comp right).pair
      ((Primrec.list_cons.comp head left).pair (Primrec.list_tail.comp right)))
  have hw : Primrec (fun z : α × Nat => (q z.1, z.2, (c z.1).2.2.1, (c z.1).2.2.2)) :=
    (hq.comp Primrec.fst).pair (Primrec.snd.pair ((left.comp Primrec.fst).pair (right.comp Primrec.fst)))
  have h := Primrec.sumCasesOn ha
    (Primrec.cond Primrec.snd (hr.comp Primrec.fst) (hl.comp Primrec.fst)).to₂ hw.to₂
  exact h.of_eq (fun x => by cases a x with | inl b => cases b <;> rfl | inr b => rfl)

private theorem pr_step : Primrec (fun z : Table × Raw => step z.1 z.2) := by
  have hl : Primrec (fun z : Table × Raw => lookup z.1 z.2.1 z.2.2.1) := pr_lookup.comp (Primrec.fst.pair
    ((Primrec.fst.comp Primrec.snd).pair ((Primrec.fst.comp Primrec.snd).comp Primrec.snd)))
  exact Primrec.option_map hl
    (pr_execute (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst)).to₂

private def tick (p : Table) (s : Raw × Bool) : Raw × Bool :=
  bif s.2 then s else match step p s.1 with
    | none => (s.1, true)
    | some c => (c, false)

private def result (s : Raw × Bool) : Option Raw := bif s.2 then some s.1 else none

private theorem pr_tick : Primrec (fun z : Table × (Raw × Bool) => tick z.1 z.2) := by
  have hc : Primrec (fun z : Table × (Raw × Bool) => z.2.1) := Primrec.fst.comp Primrec.snd
  have hs := pr_step.comp (Primrec.fst.pair hc)
  have hcase := Primrec.option_casesOn hs (hc.pair (Primrec.const true))
    (Primrec.snd.pair (Primrec.const false)).to₂
  exact (Primrec.cond (Primrec.snd.comp Primrec.snd) Primrec.snd hcase).of_eq (fun z => by cases hb : z.2.2 <;> cases hs : step z.1 z.2.1 <;> simp [tick, hb, hs])

private theorem pr_result : Primrec result :=
  Primrec.cond Primrec.snd (Primrec.option_some.comp Primrec.fst) (Primrec.const none)

private theorem tick_halted (p : Table) (c : Raw) (n : Nat) :
    (tick p)^[n] (c, true) = (c, true) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply, tick, ih]

private theorem bounded_iterate (p : Table) (n : Nat) (c : Raw) :
    bounded p n c = result ((tick p)^[n] (c, false)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    cases hs : step p c with
    | none => simp [bounded, hs, Function.iterate_succ_apply, tick, tick_halted, result]
    | some d => simpa [bounded, hs, Function.iterate_succ_apply, tick] using ih d

private theorem pr_bounded : Primrec (fun z : Table × Nat × Raw => bounded z.1 z.2.1 z.2.2) := by
  have hiter : Primrec (fun z : Table × Nat × Raw =>
      (tick z.1)^[z.2.1] (z.2.2, false)) :=
    Primrec.nat_iterate (Primrec.fst.comp Primrec.snd)
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.const false))
      (pr_tick.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact (pr_result.comp hiter).of_eq (fun z => (bounded_iterate z.1 z.2.1 z.2.2).symm)

private theorem pr_initial : Primrec (fun z : Table × List Bool => initial z.1 z.2) := by
  have hm : Primrec (fun z : Table × List Bool => z.2.map inputSymbol) :=
    Primrec.list_map Primrec.snd ((Primrec.dom_bool inputSymbol).comp Primrec.snd).to₂
  exact ((Primrec.fst.comp Primrec.snd).comp Primrec.fst).pair ((Primrec.list_headI.comp hm).pair
    ((Primrec.const []).pair (Primrec.list_tail.comp hm)))

theorem effectiveBoundedSimulation : EffectiveBoundedSimulation := by
  have hd := effectiveDecoding.1.comp (Primrec.fst : Primrec (fun z : Nat × Nat × List Bool => z.1))
  exact pr_bounded.comp (hd.pair ((Primrec.fst.comp Primrec.snd).pair
    (pr_initial.comp (hd.pair (Primrec.snd.comp Primrec.snd)))))

private theorem symbol_head (p : Table) (xs : List Nat) :
    (xs.map (symbol p)).headI = symbol p xs.headI := by
  cases xs with
  | nil =>
    apply Fin.ext
    change (0 : Nat) = 0 % width p
    simp
  | cons a xs => rfl

private theorem lookup_mod (p : Table) (q a : Nat) :
    lookup p q (symbol p a).val = lookup p q a := by
  simp [lookup, symbol]

theorem exactSingleStep : ExactSingleStep := by
  intro p c
  simp only [step, TM0.step, machine, toCfg, lookup_mod]
  cases h : lookup p c.1 c.2.1 with
  | none => rfl
  | some x =>
    rcases x with ⟨q, a⟩
    cases a with
    | inl b => cases b <;> simp [toCfg, execute, actionStmt, Tape.move, symbol_head]
    | inr b => rfl

private theorem run_zero {p : Table} {c d : Raw} (h : Run p c d 0) : c = d := by
  cases h
  rfl

theorem exactBoundedSimulation : ExactBoundedSimulation := by
  intro p fuel
  induction fuel with
  | zero => intro c d; simp [bounded]
  | succ n ih =>
    intro c d
    cases hs : step p c with
    | none =>
      constructor
      · intro h
        have eq : c = d := Option.some.inj (by simpa [bounded, hs] using h)
        subst d
        exact ⟨0, by omega, Run.refl c, hs⟩
      · rintro ⟨m, hm, hr, hd⟩
        cases hr with
        | refl => simp [bounded, hs]
        | next he _ => simp [hs] at he
    | some c' =>
      constructor
      · intro h
        obtain ⟨m, hm, hr, hd⟩ := (ih c' d).1 (by simpa [bounded, hs] using h)
        exact ⟨m + 1, by omega, Run.next hs hr, hd⟩
      · rintro ⟨m, hm, hr, hd⟩
        cases hr with
        | refl => simp [hs] at hd
        | @next _ e _ t he hr =>
          have eq : c' = e := Option.some.inj (hs.symm.trans he)
          subst e
          simpa [bounded, hs] using (ih c' d).2 ⟨t, by omega, hr, hd⟩

theorem exactInitialTape : ExactInitialTape := by
  intro p xs
  have hz : symbol p 0 = default := by
    apply Fin.ext
    change 0 % width p = 0
    simp
  cases xs <;> simp [toCfg, initial, Tape.mk₁, Tape.mk₂, Tape.mk', hz, List.map_map, Function.comp_def]

theorem literalInputSymbols : LiteralInputSymbols := by
  intro p
  have h1 : 1 < width p := by unfold width; omega
  have h2 : 2 < width p := by unfold width; omega
  simp [symbol, inputSymbol, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]

end LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetProof
