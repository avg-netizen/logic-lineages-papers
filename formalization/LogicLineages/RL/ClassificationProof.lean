module

public import LogicLineages.RL.ClassificationTargets
public import LogicLineages.RL.NegativeTransformationProof
public import LogicLineages.RL.SingletonProof

@[expose] public section

namespace LogicLineages.RL.Policy.ClassificationProof

theorem classification (S : Alphabet) : Targets.Classification S := by
  classical
  intro source sourceEnv target targetEnv
  constructor
  · intro hT
    constructor
    · by_contra hn
      have hs : Subsingleton S.Action := ⟨fun a b => by
        by_contra hab
        exact hn ⟨a, b, hab⟩⟩
      exact SingletonProof.singletonNoTransformation S hs source sourceEnv target targetEnv hT
    · cases source <;> cases target
      · exact Or.inl rfl
      · exact Or.inl rfl
      · exact False.elim (NegativeTransformationProof.negativeTransformation S sourceEnv targetEnv hT)
      · exact Or.inr rfl
  · rintro ⟨ha, ht⟩
    exact PositiveTransformationProof.positiveTransformation S source sourceEnv target targetEnv ha ht

end LogicLineages.RL.Policy.ClassificationProof
