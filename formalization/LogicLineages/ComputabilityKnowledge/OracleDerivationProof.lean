module

public import LogicLineages.ComputabilityKnowledge.OracleDerivationTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleDerivationProof
open OracleProgram OracleDerivation OracleDerivationTargets

private theorem prec_zero (g : Nat → Part Nat) (p q : Program) (a : Nat) :
    eval g (.prec p q) (Nat.pair a 0) = eval g p a := by simp [eval]

private theorem prec_succ (g : Nat → Part Nat) (p q : Program) (a n : Nat) :
    eval g (.prec p q) (Nat.pair a (n + 1)) =
      (eval g (.prec p q) (Nat.pair a n)).bind fun v => eval g q (Nat.pair a (Nat.pair n v)) := by
  simp [eval]

theorem finiteDerivationSound : FiniteDerivationSound := by
  intro g p input output h
  induction h with
  | base c input output fuel halts => exact Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr halts)
  | query input => exact Part.mem_some_iff.mpr rfl
  | pair hp hq ihp ihq =>
      change _ ∈ Nat.pair <$> _ <*> _
      rw [Part.eq_some_iff.mpr ihp, Part.eq_some_iff.mpr ihq]
      simp [Seq.seq]
  | comp hq hp ihq ihp => exact Part.mem_bind_iff.mpr ⟨_, ihq, ihp⟩
  | precZero hp ih => simpa only [prec_zero] using ih
  | precSucc hprev hstep ihprev ihstep =>
      rw [prec_succ]
      exact Part.mem_bind_iff.mpr ⟨_, ihprev, ihstep⟩
  | mu prior runs nonzero last ihRuns ihLast =>
      apply Nat.mem_rfind.mpr
      constructor
      · exact (Part.mem_map_iff _).mpr ⟨0, ihLast, by decide⟩
      · intro j hj
        exact (Part.mem_map_iff _).mpr ⟨prior.getD j 0, ihRuns j hj, by exact decide_eq_false (nonzero j hj)⟩

theorem finiteDerivationComplete : FiniteDerivationComplete := by
  classical
  intro g p
  induction p with
  | base c =>
      intro input output h
      obtain ⟨fuel, hf⟩ := Nat.Partrec.Code.evaln_complete.mp h
      exact .base c input output fuel (Option.mem_def.mp hf)
  | query =>
      intro input output h
      have heq : output = g input := Part.mem_some_iff.mp h
      subst output
      exact .query input
  | pair p q ihp ihq =>
      intro input output h
      simp only [eval, Seq.seq, Bind.bind, Part.bind_map, Part.mem_bind_iff, Part.mem_map_iff, Part.mem_some_iff] at h
      obtain ⟨a, ha, b, hb, hout⟩ := h
      obtain ⟨av, hav, heqa⟩ := (Part.mem_map_iff _).mp ha
      subst a
      subst output
      exact .pair (ihp _ _ hav) (ihq _ _ hb)
  | comp p q ihp ihq =>
      intro input output h
      obtain ⟨middle, hq, hp⟩ := Part.mem_bind_iff.mp h
      exact .comp (ihq _ _ hq) (ihp _ _ hp)
  | prec p q ihp ihq =>
      have H : ∀ a n output, output ∈ eval (fun x => Part.some (g x)) (.prec p q) (Nat.pair a n) →
          Derives g (.prec p q) (Nat.pair a n) output := by
        intro a n
        induction n with
        | zero =>
            intro output h
            rw [prec_zero] at h
            exact .precZero (ihp _ _ h)
        | succ n ih =>
            intro output h
            rw [prec_succ] at h
            obtain ⟨previous, hprev, hstep⟩ := Part.mem_bind_iff.mp h
            exact .precSucc (ih _ hprev) (ihq _ _ hstep)
      intro input output h
      have hh := H input.unpair.1 input.unpair.2 output
      simpa only [Nat.pair_unpair] using hh (by simpa only [Nat.pair_unpair] using h)
  | mu p ih =>
      intro input output h
      have hfind := Nat.mem_rfind.mp h
      obtain ⟨zeroValue, hz, hzero⟩ := (Part.mem_map_iff _).mp hfind.1
      have hz0 : zeroValue = 0 := by simpa using hzero
      subst zeroValue
      have H : ∀ j : Fin output, ∃ v : Nat,
          v ∈ eval (fun x => Part.some (g x)) p (Nat.pair input j) ∧ v ≠ 0 := by
        intro j
        obtain ⟨v, hv, heq⟩ := (Part.mem_map_iff _).mp (hfind.2 j.isLt)
        exact ⟨v, hv, by simpa using heq⟩
      choose values hvalues using H
      let prior := List.ofFn values
      have hlen : prior.length = output := List.length_ofFn
      have hget : ∀ j (hj : j < output), prior.getD j 0 = values ⟨j, hj⟩ := by
        intro j hj
        simp only [prior, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hj, Option.getD_some]
      have hd : Derives g (.mu p) input prior.length := by
        apply Derives.mu prior
        · intro j hj
          have hj' : j < output := by simpa [hlen] using hj
          rw [hget j hj']
          exact ih _ _ (hvalues ⟨j, hj'⟩).1
        · intro j hj
          have hj' : j < output := by simpa [hlen] using hj
          rw [hget j hj']
          exact (hvalues ⟨j, hj'⟩).2
        · rw [hlen]
          exact ih _ _ hz
      simpa only [hlen] using hd

theorem finiteDerivationUnique : FiniteDerivationUnique := by
  intro g p input left right hl hr
  exact Part.mem_unique (finiteDerivationSound g p input left hl) (finiteDerivationSound g p input right hr)

end LogicLineages.ComputabilityKnowledge.OracleDerivationProof
