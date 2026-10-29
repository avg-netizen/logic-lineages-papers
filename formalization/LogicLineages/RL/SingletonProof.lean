module

public import LogicLineages.RL.ClassificationTargets
public import LogicLineages.RL.PolicySemanticsProof

@[expose] public section

namespace LogicLineages.RL.Policy.SingletonProof

variable {S : Alphabet}

theorem singleton_mass [Subsingleton S.Action] (k : Kernel S.Action) (a : S.Action) :
    k.mass a = 1 := by
  classical
  have hs := k.sum_one
  have he : (∑ b : S.Action, k.mass b) = k.mass a := by
    apply Finset.sum_eq_single a
    · intro b hb hba
      exact False.elim (hba (Subsingleton.elim b a))
    · simp
  rw [he] at hs
  exact hs

theorem singleton_agent [Subsingleton S.Action] (kind : Kind) (p q : Agent S kind) : p = q := by
  cases kind with
  | deterministic => funext h; exact Subsingleton.elim _ _
  | stochastic =>
      funext h
      apply PolicySemanticsProof.kernel_ext
      intro a
      rw [singleton_mass, singleton_mass]

theorem singletonNoTransformation (S : Alphabet) : Targets.SingletonNoTransformation S := by
  intro hsub source sourceEnv target targetEnv hT
  letI := hsub
  obtain ⟨T⟩ := hT
  obtain ⟨p, q, μ, hlt⟩ := T.agentsSeparated
  have he := singleton_agent target (T.agentMap p) (T.agentMap q)
  rw [he] at hlt
  exact (lt_irrefl _ hlt)

end LogicLineages.RL.Policy.SingletonProof
