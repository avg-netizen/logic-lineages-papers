module
public import LogicLineages.OrdinalComparison.PositiveNormalFlagTargets
public import LogicLineages.OrdinalComparison.EncodedCollectedNormalizeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

theorem positiveNormalFlagComputable : Targets.PositiveNormalFlagComputable := by
  have hb : Computable₂ (fun n m : Nat => n==m) := Primrec.beq.to_comp
  exact hb.comp (encodedCollectedNormalizeComputable.comp Computable.fst)
    (encodedCollectedNormalizeComputable.comp Computable.snd)

theorem positiveNormalFlagCorrect : Targets.PositiveNormalFlagCorrect := by
  intro E F hE hF
  unfold encodedPositiveNormalFormsEqual
  rw [encodedCollectedNormalizeCorrect E hE,encodedCollectedNormalizeCorrect F hF,beq_iff_eq]
  exact collectedPositiveCodeInjective.1.eq_iff

end LogicLineages.OrdinalComparison
