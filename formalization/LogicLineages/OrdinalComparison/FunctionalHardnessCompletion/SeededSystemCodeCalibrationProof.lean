module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSourceCodeCalibrationProof
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeCalibrationProof
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode.Proof
open OriginalDomain FunctionalDetector
open SeededSourceCode (appCode lamCode weakenCode combineCode)

private theorem app_correct {Γ : List Ty} {σ τ : Ty}
    (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ) :
    appCode (SyntaxCode.encodeTerm f) (SyntaxCode.encodeTerm a) =
      SyntaxCode.encodeTerm (.app f a) := rfl

private theorem align_correct {Γ : List Ty} (a : OriginalTerm Γ unary)
    (z : OriginalTerm Γ .ground) :
    alignCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm z) =
      SyntaxCode.encodeTerm (FunctionalDetector.pad a z) := by
  have h := ContextInsertionCode.Proof.exactSourceInsertion [] [.ground] Γ unary a
  change weakenCode (SyntaxCode.encodeTerm a) =
    SyntaxCode.encodeTerm (a.rename (Renaming.weaken Γ .ground)) at h
  unfold alignCode
  rw [h]
  rfl

private theorem payload_correct {Γ : List Ty} (a b : OriginalTerm Γ unary) :
    payloadCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
      SyntaxCode.encodeTerm (payload a b) := by
  simp only [payloadCode, payload, ← app_correct, ← SeededSourceCode.Proof.combine_correct]
  rfl

private theorem left_correct {Γ : List Ty} (a b : OriginalTerm Γ unary) :
    leftCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
      SyntaxCode.encodeTerm (left a b) := by
  unfold leftCode
  rw [payload_correct, SeededSourceCode.Proof.combine_correct,
    SeededSourceCode.Proof.combine_correct, app_correct, app_correct,
    SourceGammaAggregateCode.Proof.eraser_correct]
  rfl

private theorem right_correct {Γ : List Ty} (a b : OriginalTerm Γ unary) :
    rightCode (SyntaxCode.encodeTerm a) (SyntaxCode.encodeTerm b) =
      SyntaxCode.encodeTerm (right a b) := by
  unfold rightCode
  rw [payload_correct, SeededSourceCode.Proof.combine_correct,
    SeededSourceCode.Proof.combine_correct, app_correct, app_correct,
    SourceGammaAggregateCode.Proof.eraser_correct]
  rfl

private theorem shift_two_correct {Γ : List Ty} {τ : Ty} (a : OriginalTerm Γ τ) :
    ContextInsertionCode.sourceCode 0 2 (SyntaxCode.encodeTerm a) =
      SyntaxCode.encodeTerm (a.rename (shiftTwo Γ)) :=
  SourcePlanPrefixCode.Proof.prefix_correct 2 (shiftTwo Γ) (fun _ _ => rfl) a

theorem exactDetectorCode : Targets.ExactDetectorCode := by
  intro Γ a b
  unfold detectorCode SourcePlanPrefixCode.shiftPair
  simp only [shift_two_correct]
  have hz : (0 : Nat) = SyntaxCode.encodeTerm
      (.var .here : OriginalTerm (.ground :: .ground :: Γ) .ground) := rfl
  have hw : (8 : Nat) = SyntaxCode.encodeTerm
      (.var (.there .here) : OriginalTerm (.ground :: .ground :: Γ) .ground) := rfl
  rw [hz, hw, align_correct, align_correct, left_correct, right_correct]
  rfl

theorem exactContextAndEmbedding : Targets.ExactContextAndEmbedding := by
  intro n s
  induction s with
  | nil => simp [SeededSystem.compile]
  | cons d ds ih =>
      constructor
      · change .ground :: .ground :: (SeededSystem.compile ds).context =
          List.replicate (2 * (ds.length + 1)) .ground ++ SignedPair.Context n
        rw [ih.1]
        have h : 2 * (ds.length + 1) = Nat.succ (Nat.succ (2 * ds.length)) := by omega
        rw [h]
        rfl
      · intro τ x
        change SourceTypedPorts.variableIndex ((SeededSystem.compile ds).original x) + 1 + 1 =
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
      rw [SeededInputCode.Proof.exactSubtractSeed, SeededSourceCode.Proof.exactCompilerCalibration]
      dsimp only
      let p := (SeededCompiler.compile (SeededCompiler.subtractSeed d)).pair
      let tail := SeededSystem.compile ds
      have hp : SourcePlanPrefixCode.shiftPair (2 * ds.length) (SeededSourceCode.pairCode p) =
          (SyntaxCode.encodeTerm (p.1.rename tail.original),
            SyntaxCode.encodeTerm (p.2.rename tail.original)) := by
        unfold SourcePlanPrefixCode.shiftPair SeededSourceCode.pairCode
        rw [SourcePlanPrefixCode.Proof.prefix_correct _ tail.original
          (exactContextAndEmbedding n ds).2,
          SourcePlanPrefixCode.Proof.prefix_correct _ tail.original
          (exactContextAndEmbedding n ds).2]
      rw [hp, exactDetectorCode]
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
      SourceGammaAggregateCode.pairCode (SeededSystem.strictPair s) := by
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

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode.Proof
