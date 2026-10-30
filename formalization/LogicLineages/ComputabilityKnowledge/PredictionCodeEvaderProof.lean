module

public import LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderTargets
public import LogicLineages.ComputabilityKnowledge.PredictionUniformHistoryProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderProof
open PredictionGame PredictionLearning PredictionRobust PredictionSelfHistory PredictionUniformHistory
open PredictionCodeEvader PredictionCodeEvaderTargets

private theorem some_iff_index (xs : List Bool) (k : Nat) :
    completedCode xs = some k ↔ xs.findIdx Bool.not = k ∧ k < xs.length := by
  by_cases h : xs.findIdx Bool.not < xs.length
  · simp only [completedCode, if_pos h, Option.some.injEq]
    constructor
    · intro heq; exact ⟨heq, heq ▸ h⟩
    · exact And.left
  · simp only [completedCode, if_neg h, reduceCtorEq, false_iff]
    rintro ⟨heq, hk⟩
    exact h (heq.symm ▸ hk)

theorem completedCodeSpecification : CompletedCodeSpecification := by
  intro xs
  constructor
  · constructor
    · intro hn b hb
      have hlen : xs.findIdx Bool.not = xs.length := by
        have hle := List.findIdx_le_length (p := Bool.not) (xs := xs)
        by_contra hne
        have hlt : xs.findIdx Bool.not < xs.length := by omega
        simp only [completedCode, if_pos hlt, reduceCtorEq] at hn
      have hfalse := List.findIdx_eq_length.mp hlen b hb
      cases b <;> simp_all
    · intro hall
      have hlen := List.findIdx_eq_length_of_false (p := Bool.not) (xs := xs)
        (fun b hb => by rw [hall b hb]; rfl)
      simp [completedCode, hlen]
  · intro k
    rw [some_iff_index]
    constructor
    · rintro ⟨heq, hk⟩
      have hs := (List.findIdx_eq (p := Bool.not) hk).mp heq
      have hv : xs[k] = false := by simpa using hs.1
      refine ⟨hk, ?_, ?_⟩
      · simp only [List.getElem?_eq_getElem hk, hv]
      · intro i hi
        have hi' : i < xs.length := by omega
        have hv' : xs[i] = true := by simpa using hs.2 i hi
        simp only [List.getElem?_eq_getElem hi', hv']
    · rintro ⟨hk, hv, hprev⟩
      refine ⟨(List.findIdx_eq (p := Bool.not) hk).mpr ⟨?_, ?_⟩, hk⟩
      · have hv' : xs[k] = false := by simpa only [List.getElem?_eq_getElem hk, Option.some.injEq] using hv
        simp [hv']
      · intro i hi
        have hi' : i < xs.length := by omega
        have hv' : xs[i] = true := by
          simpa only [List.getElem?_eq_getElem hi', Option.some.injEq] using hprev i hi
        simp [hv']

theorem completedCodePermanent : CompletedCodePermanent := by
  intro xs ys k hk
  obtain ⟨hidx, hlen⟩ := (some_iff_index xs k).mp hk
  apply (some_iff_index (xs ++ ys) k).mpr
  constructor
  · rw [List.findIdx_append, if_pos (by rw [hidx]; exact hlen), hidx]
  · simp only [List.length_append]
    omega

theorem completedCodePrimitiveRecursive : CompletedCodePrimitiveRecursive := by
  have hf : Primrec (fun xs : List Bool => xs.findIdx Bool.not) :=
    Primrec.list_findIdx Primrec.id ((Primrec.dom_bool Bool.not).comp Primrec.snd).to₂
  exact Primrec.ite (Primrec.nat_lt.comp hf Primrec.list_length)
    (Primrec.option_some.comp hf) (Primrec.const none)

private theorem stream (k : Nat) (p : Policy) (n : Nat) :
    evasion p (codePolicy k) n = decide (n < k) := by
  simp only [evasion, codePolicy, (history_lengths p (codePolicy k) n).2]

private theorem prefix_snoc {α : Type} (s : Nat → α) (n : Nat) :
    historyPrefix s (n + 1) = historyPrefix s n ++ [s n] := List.ofFn_succ_last

private theorem code_history (k : Nat) (p : Policy) (n : Nat) :
    (histories p (codePolicy k) n).evasions = historyPrefix (fun i => decide (i < k)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [evasion_prefix, ih, stream]
    rw [prefix_snoc]

theorem codeEvaderStream : CodeEvaderStream := by
  intro k p n
  refine ⟨stream k p n, ?_⟩
  rw [code_history]
  by_cases hk : k < n
  · rw [if_pos hk]
    apply (completedCodeSpecification _).2 k |>.mpr
    refine ⟨by simp [historyPrefix]; exact hk, ?_, ?_⟩
    · simp [historyPrefix, List.getElem?_ofFn, hk]
    · intro i hi
      have hin : i < n := by omega
      simp [historyPrefix, List.getElem?_ofFn, hin, hi]
  · rw [if_neg hk]
    apply (completedCodeSpecification _).1.mpr
    intro b hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    subst b
    have hik : (i : Nat) < k := by omega
    simp [hik]

theorem uniformCodeEvaderProgram : UniformCodeEvaderProgram := by
  let R : ParameterRule := fun k xs _ => codePolicy k xs
  have hR : Computable (fun q : Nat × List Bool × List Bool => R q.1 q.2.1 q.2.2) :=
    (Primrec.nat_lt.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst).decide.to_comp
  obtain ⟨u, hu, _, hsem⟩ := PredictionUniformHistoryProof.uniformSelfHistoryProgram R hR
  refine ⟨u, hu, ?_⟩
  intro k
  obtain ⟨_, he, heq⟩ := hsem k
  exact ⟨he, heq⟩

theorem completedCodeActualStabilization : CompletedCodeActualStabilization := by
  classical
  intro p e
  by_cases hall : ∀ n : Nat, completedCode (histories p e n).evasions = none
  · exact Or.inl hall
  · obtain ⟨N, hN⟩ := not_forall.mp hall
    cases hc : completedCode (histories p e N).evasions with
    | none => exact False.elim (hN hc)
    | some k =>
      refine Or.inr ⟨N, k, ?_⟩
      intro n hn
      induction n, hn using Nat.le_induction with
      | base => exact hc
      | succ n hn ih =>
        rw [evasion_prefix]
        exact completedCodePermanent _ _ k ih

end LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderProof
