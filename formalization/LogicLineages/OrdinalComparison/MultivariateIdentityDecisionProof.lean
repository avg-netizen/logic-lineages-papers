module
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionTargets
public import LogicLineages.OrdinalComparison.MultivariateProbeCodeProof
public import LogicLineages.OrdinalComparison.MultivariateFreshProbeProof
public import LogicLineages.OrdinalComparison.PositiveUnaryIdentityProof
public import LogicLineages.OrdinalComparison.PositiveInputPlugProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateIdentityDecision

theorem flag_computable : Computable₂ encodedMultivariateIdentity := by
  have hn : Computable (fun p : Nat × Nat => p.1) := Computable.fst
  have hm : Computable (fun p : Nat × Nat => p.2) := Computable.snd
  have hcap := Primrec.nat_max.to_comp.comp hn hm
  exact positiveNormalFlagComputable.comp
    (MultivariateProbeCode.primitive.to_comp.comp hcap hn)
    (MultivariateProbeCode.primitive.to_comp.comp hcap hm)

theorem counter_input_computable : Computable₂ encodedMultivariateProbeCounterInput := by
  have hn : Computable (fun p : Nat × Nat => p.1) := Computable.fst
  have hm : Computable (fun p : Nat × Nat => p.2) := Computable.snd
  have hcap := Primrec.nat_max.to_comp.comp hn hm
  exact actualPositiveUnaryIdentity.2.2.1.comp
    (MultivariateProbeCode.primitive.to_comp.comp hcap hn)
    (MultivariateProbeCode.primitive.to_comp.comp hcap hm)

theorem weight_computable :
    Computable (fun p : Nat × Nat × Nat => encodedMultivariateCounterWeight p.1 p.2.1 p.2.2) := by
  have hn : Computable (fun p : Nat × Nat × Nat => p.1) := Computable.fst
  have hm : Computable (fun p : Nat × Nat × Nat => p.2.1) := Computable.fst.comp Computable.snd
  have hi : Computable (fun p : Nat × Nat × Nat => p.2.2) := Computable.snd.comp Computable.snd
  have hcap := Primrec.nat_max.to_comp.comp hn hm
  exact encodedPositiveEvaluationComputable.comp
    (MultivariateProbeCode.literal_primitive.to_comp.comp hcap hi)
    (counter_input_computable.comp hn hm)

theorem decision : Targets.MultivariateIdentityDecision := by
  refine ⟨flag_computable,counter_input_computable,weight_computable,?_⟩
  intro d E F hE hF
  let n := multivariatePositiveEncode E
  let m := multivariatePositiveEncode F
  let cap := max n m
  let PE := multivariatePositiveProbe cap E
  let PF := multivariatePositiveProbe cap F
  let v := encodedMultivariateProbeCounterInput n m
  have hcE : multivariatePositiveEncode E≤cap := Nat.le_max_left n m
  have hcF : multivariatePositiveEncode F≤cap := Nat.le_max_right n m
  have hpE : fixedLimitProfileBelow epsilonZero PE := MultivariateFreshProbe.source.1 d cap E hE
  have hpF : fixedLimitProfileBelow epsilonZero PF := MultivariateFreshProbe.source.1 d cap F hF
  have hflag : encodedMultivariateIdentity n m=
      encodedPositiveNormalFormsEqual (positiveExprEncode PE) (positiveExprEncode PF) := by
    unfold encodedMultivariateIdentity
    rw [MultivariateProbeCode.correct cap E,MultivariateProbeCode.correct cap F]
  have hcounter : v=encodedPositiveCounterInput (positiveExprEncode PE) (positiveExprEncode PF) := by
    dsimp only [v,encodedMultivariateProbeCounterInput]
    rw [MultivariateProbeCode.correct cap E,MultivariateProbeCode.correct cap F]
  have hw (i : Nat) : encodedMultivariateCounterWeight n m i=
      actualProfileHead (positiveVariableHead cap i) v := by
    unfold encodedMultivariateCounterWeight
    rw [MultivariateProbeCode.literal_code cap i,encodedPositiveEvaluationCorrect]
    rfl
  have hu := actualPositiveUnaryIdentity.2.2.2 PE PF hpE hpF
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro h ρ _
    have hnf : collectedPositiveNormalize PE=collectedPositiveNormalize PF :=
      (positiveNormalFlagCorrect PE PF hpE hpF).mp (hflag.symm.trans h)
    have hrE := MultivariateFreshProbe.retraction d cap E hE hcE ρ 0
    have hrF := MultivariateFreshProbe.retraction d cap F hF hcF ρ 0
    rw [hnf] at hrE
    exact hrE.symm.trans hrF
  · intro h
    rw [hflag]
    apply hu.2.2.2.1.mpr
    intro x _
    rw [MultivariateFreshProbe.source.2.1 cap x E,MultivariateFreshProbe.source.2.1 cap x F]
    exact h _ (fun i _ => MultivariateFreshProbe.head_source.2.2 cap i x)
  · intro hfalse
    have hne := hu.2.2.2.2 (hflag.symm.trans hfalse)
    rw [← hcounter] at hne
    refine ⟨?_,?_⟩
    · intro i
      rw [hw i]
      exact MultivariateFreshProbe.head_source.2.2 cap i v
    · have hfun : encodedMultivariateCounterWeight n m=
          (fun i => actualProfileHead (positiveVariableHead cap i) v) := funext hw
      rw [hfun,← MultivariateFreshProbe.source.2.1 cap v E,
        ← MultivariateFreshProbe.source.2.1 cap v F]
      exact hne

end LogicLineages.OrdinalComparison.MultivariateIdentityDecision
