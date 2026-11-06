module
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.TerminalProof
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.RunnerSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
open PolynomialGraphCompletion WordGuardCompletion CanonicalGuardSelector
open GuardChildMeasureCompletion ComparisonProof

theorem compile_eq (D : Nat) (p : WordPair) (hp : admitted D p = true) :
    compile D p = finish p (leastFuel D p) := by
  simp only [compile,if_pos hp]

theorem compilerCalibration : Targets.CompilerCalibration := by
  intro D p
  constructor
  · intro hp
    simp [compile,hp]
  · intro hp
    have hleast := RunnerProof.leastFuelCorrect D p
    refine ⟨compile_eq D p hp,(hleast.2.2.2 hp).1,?_⟩
    intro n hn hterminal
    have hfalse := hleast.2.1 n hn
    simp [stopped,hp,hterminal] at hfalse

theorem finish_paid (p : WordPair) (n : Nat) :
    paidTail (run p n) ≤ packageTail (finish p n) := Nat.le_max_left _ _

theorem finish_terminal (p : WordPair) (n : Nat) :
    terminalTail (run p n).1 ≤ packageTail (finish p n) := Nat.le_max_right _ _

theorem finish_accumulated (p : WordPair) (n : Nat) :
    (run p n).2.1 ≤ packageTail (finish p n) :=
  (show (run p n).2.1 ≤ paidTail (run p n) from Nat.le_max_left _ _).trans (finish_paid p n)

theorem finiteTrace_mem (p q : WordPair) (n : Nat) :
    q ∈ finiteTrace p n ↔ ∃ k, k ≤ n ∧ (run p k).1 = q := by
  constructor
  · intro h
    obtain ⟨k,hk,hq⟩ := List.mem_map.mp h
    exact ⟨k,Nat.le_of_lt_succ (List.mem_range.mp hk),hq⟩
  · rintro ⟨k,hk,hq⟩
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr (Nat.lt_succ_of_le hk),hq⟩

theorem initial_in_trace (p : WordPair) (n : Nat) : p ∈ finiteTrace p n :=
  (finiteTrace_mem p p n).mpr ⟨0,Nat.zero_le n,rfl⟩

theorem finiteTrace_admitted (D : Nat) (p : WordPair) (hp : admitted D p = true)
    (n : Nat) : ∀ q ∈ finiteTrace p n, admitted D q = true := by
  intro q hq
  obtain ⟨k,_hk,hq⟩ := (finiteTrace_mem p q n).mp hq
  rw [← hq]
  exact RunnerProof.runAdmission D p hp k

theorem compiledSyntax : Targets.CompiledSyntax := by
  intro D p _hD hp
  simp only [compile_eq D p hp]
  let n := leastFuel D p
  have hs := terminalSyntax D (run p n).1 (RunnerProof.runAdmission D p hp n)
  refine ⟨hs.1,hs.2,?_,?_,initial_in_trace p n,finiteTrace_admitted D p hp n⟩
  · intro desired sign hd hsign
    change sign ∈ guardAt (makeGuards (run p n).2.2) desired at hsign
    rw [guardAt_makeGuards _ _ hd] at hsign
    exact ((signFormula_mem _ _ _).mp hsign).1
  · exact liftTie_bound _ _ (RunnerProof.runTieBound p n) (terminalSame_bound (run p n).1)

theorem compiledDomains : Targets.CompiledDomains := by
  intro D p _hD hp x y hx hy
  simp only [compile_eq D p hp] at hx hy ⊢
  let n := leastFuel D p
  have hpx := (finish_paid p n).trans hx
  have hpy := (finish_paid p n).trans hy
  have htrace := RunnerProof.traceDomains D p hp n x y hpx hpy
  have hzero := htrace 0 (Nat.zero_le n)
  have hlast := htrace n (Nat.le_refl n)
  refine ⟨hzero.1,hzero.2,terminalRow_domain (run p n).1 x y hlast.2,?_⟩
  intro q hq
  obtain ⟨k,hk,hq⟩ := (finiteTrace_mem p q n).mp hq
  rw [← hq]
  have hd := htrace k hk
  have ha := (RunnerProof.admissionCorrect D (run p k).1).mp
    (RunnerProof.runAdmission D p hp k)
  exact ⟨hd.1,hd.2,
    (CanonicalGuardSelector.Proof.viewCorrect D (run p k).1.1 x ha.1 hd.1).1,
    (CanonicalGuardSelector.Proof.viewCorrect D (run p k).1.2 y ha.2 hd.2).1⟩

end LogicLineages.OrdinalComparison.FullWordGuardCompletion.Proof
