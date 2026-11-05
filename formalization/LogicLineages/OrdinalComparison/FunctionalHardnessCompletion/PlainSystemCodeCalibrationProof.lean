module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.PlainSystemCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode.Proof
open OriginalDomain FunctionalDetector SignedPair
open SeededSourceCode (expressionCode compilerCode unitCode pairCode addStep negStep omegaStep)

private theorem mod_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) % 6 = tag := by omega
private theorem div_tag (a tag : Nat) (h : tag < 6) : (6 * a + tag) / 6 = a := by omega

theorem exactPlainCompiler : Targets.ExactPlainCompiler := by
  intro n d
  induction d with
  | unit =>
      rw [expressionCode, compilerCode]
      change (unitCode, 12) = (pairCode (@unitPair (Context n)), 12)
      rw [(SeededSourceCode.Proof.exactLeaves.1 (Context n)).1]
  | var i =>
      rw [expressionCode, compilerCode]
      simp only [mod_tag _ 1 (by decide), div_tag _ 1 (by decide), i.isLt, ↓reduceIte]
      change (SeededSourceCode.variableCode i.val, 15) = (pairCode (variablePair i), 15)
      rw [SeededSourceCode.Proof.variable_correct i]
  | add a b iha ihb =>
      rw [expressionCode, compilerCode]
      simp [mod_tag _ 2 (by decide), div_tag _ 2 (by decide), Nat.unpair_pair,
        iha, ihb, addStep, SignedPair.compile, SeededSourceCode.Proof.pad_correct,
        SeededSourceCode.Proof.join_correct]
  | neg a ih =>
      rw [expressionCode, compilerCode]
      simp [mod_tag _ 3 (by decide), div_tag _ 3 (by decide),
        ih, negStep, SignedPair.compile, pairCode]
  | shift a ih =>
      rw [expressionCode, compilerCode]
      simp [mod_tag _ 4 (by decide), div_tag _ 4 (by decide),
        ih, omegaStep, SignedPair.compile, pairCode, SeededSourceCode.Proof.omega_correct]

theorem exactContextAndEmbedding : Targets.ExactContextAndEmbedding := by
  intro n s
  induction s with
  | nil => simp [compileSystem]
  | cons d ds ih =>
      constructor
      · change .ground :: .ground :: (compileSystem ds).context =
          List.replicate (2 * (ds.length + 1)) .ground ++ SignedPair.Context n
        rw [ih.1]
        have h : 2 * (ds.length + 1) = Nat.succ (Nat.succ (2 * ds.length)) := by omega
        rw [h]
        rfl
      · intro τ x
        change SourceTypedPorts.variableIndex ((compileSystem ds).original x) + 1 + 1 =
          SourceTypedPorts.variableIndex x + 2 * (ds.length + 1)
        rw [ih.2 τ x]
        omega

theorem exactSystemCode : Targets.ExactSystemCode := by
  intro n s
  induction s with
  | nil => rfl
  | cons d ds ih =>
      change step n (SeededSourceCode.expressionCode d)
        (systemCode n (ds.map SeededSourceCode.expressionCode)) = _
      rw [ih]
      unfold step
      rw [exactPlainCompiler]
      dsimp only
      let p := (SignedPair.compile d).pair
      let tail := compileSystem ds
      have hp : SourcePlanPrefixCode.shiftPair (2 * ds.length) (SeededSourceCode.pairCode p) =
          (SyntaxCode.encodeTerm (p.1.rename tail.original),
            SyntaxCode.encodeTerm (p.2.rename tail.original)) := by
        unfold SourcePlanPrefixCode.shiftPair SeededSourceCode.pairCode
        rw [SourcePlanPrefixCode.Proof.prefix_correct _ tail.original
          (exactContextAndEmbedding n ds).2,
          SourcePlanPrefixCode.Proof.prefix_correct _ tail.original
          (exactContextAndEmbedding n ds).2]
      rw [hp, SeededSystemCode.Proof.exactDetectorCode]
      have ht := (SourcePlanPrefixCode.Proof.exactPrefixCalibration
        tail.context (.ground :: .ground :: tail.context) 2 (shiftTwo tail.context)
        (fun _ _ => rfl)).2 tail.detectors
      rw [ht]
      apply Prod.ext
      · simp only [List.length_cons]
        omega
      · rfl

theorem exactQueryPairs : Targets.ExactQueryPairs := by
  intro n s
  have hs : strictCode n (s.map SeededSourceCode.expressionCode) =
      SourceGammaAggregateCode.pairCode (strictSystemPair s) := by
    unfold strictCode
    rw [exactSystemCode]
    exact SourceGammaAggregateCode.Proof.exactAggregateCode _ _
  refine ⟨hs, ?_, ?_⟩
  · unfold weakCode
    rw [hs]
    rfl
  · unfold contextCode
    rw [exactSystemCode]
    change List.replicate (2 * s.length) 0 ++ List.replicate n (SyntaxCode.typeCode unary) = _
    rw [(exactContextAndEmbedding n s).1]
    simp [SignedPair.Context, SyntaxCode.typeCode]


end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode.Proof
