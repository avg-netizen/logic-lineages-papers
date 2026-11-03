module
public import LogicLineages.OrdinalComparison.UnitScalarEvaluationCodeTargets
public import LogicLineages.OrdinalComparison.UnitHeadCodeProof
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeProof
public import LogicLineages.OrdinalComparison.WWScalarTranslationProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentProof
public import LogicLineages.OrdinalComparison.WWUnaryCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitScalarEvaluationCode.Proof
open ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem exactRefusingExtraction : Targets.ExactRefusingExtraction := by
  intro Γ q
  have he : scalarCode (OrdinalSyntax.typedCode q) =
      (compileScalar (UnitHeadEvaluation.unitSyntax q)).map
        (scalarSyntaxCode (fun c => SourceTypedPorts.variableIndex c.2.1)) := by
    rw [scalarCode,UnitHeadCode.Proof.unit_exact]
    exact congrArg Prod.snd (OrdinalSyntax.ordinalSyntaxExtractionCorrect Γ (UnitHeadEvaluation.unitSyntax q))
  refine ⟨he,?_⟩
  rw [valueCode,he,Option.map_map]
  congr 1
  funext s
  simpa using scalarSyntaxValueSourceCorrect (OrdinalComponent Γ)
    (fun c => SourceTypedPorts.variableIndex c.2.1) s []

private theorem scalar_total {Γ i q} (hg : GeneratedOrdinalGrade Γ i q) :
    i = 0 → ∃ s : Scalar (OrdinalComponent Γ),
      compileScalar (UnitHeadEvaluation.unitSyntax q) = some s := by
  induction hg with
  | one i => intro _; exact ⟨.one,rfl⟩
  | omega i hi => intro he; omega
  | var x j => intro _; exact ⟨.one,rfl⟩
  | add hf hg ihf ihg =>
    intro he
    obtain ⟨a,ha⟩ := ihf he
    obtain ⟨b,hb⟩ := ihg he
    exact ⟨.add a b,by simp [UnitHeadEvaluation.unitSyntax,compileScalar,ha,hb]⟩
  | emul hi hf hg ihf ihg => intro he; omega
  | @collapse f g hf hg ihf ihg =>
    intro _
    obtain ⟨a,ha⟩ := UnitHeadEvaluation.Proof.extract_total hf (by omega)
    obtain ⟨b,hb⟩ := ihg rfl
    change extractPositive (UnitHeadEvaluation.unitSyntax f) = some a at ha
    exact ⟨.shift a b,by simp [UnitHeadEvaluation.unitSyntax,compileScalar,ha,hb]⟩

theorem effectiveGeneratedScalar : Targets.EffectiveGeneratedScalar := by
  have hs : Primrec scalarCode := Primrec.snd.comp
    (OrdinalSyntax.ordinalSyntaxExtractionPrimitiveRecursive.comp
      UnitHeadCode.Proof.primitiveRecursiveAlgorithms.1)
  have hv : Computable valueCode := by
    apply Computable.option_map hs.to_comp
    exact (scalarSyntaxValueComputable.comp
      (Computable.snd.pair (Computable.const ([] : List Nat)))).to₂
  refine ⟨hs,hv,?_⟩
  intro Γ q hg
  obtain ⟨s,hs⟩ := scalar_total hg rfl
  refine ⟨s.value (fun _ => 1),?_,?_⟩
  · rw [(exactRefusingExtraction Γ q).2,hs]
    rfl
  · have h := scalarTranslationSound Γ (UnitHeadEvaluation.unitSyntax q) s hs (fun _ => 1)
    simp only [Nat.cast_one] at h
    exact h.trans (UnitHeadEvaluation.Proof.unit_value q (fun _ => 1))

theorem actualClosedSourceScalar : Targets.ActualClosedSourceScalar := by
  intro Γ τ t
  obtain ⟨u,hu,hg⟩ := AdmissibleAssignment.actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  obtain ⟨c,hc,hval⟩ := effectiveGeneratedScalar.2.2 Γ (u 0) (hg 0)
  have hv : AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (UnaryCarrier.closeGround t) =
      some (GroundClosing.vector (UnaryCarrier.groundMap Γ) u) := by
    rw [UnaryCarrier.closeGround,GroundClosing.StatementChecks.assignmentNaturality,hu]
    rfl
  refine ⟨u,c,hu,hv,hc,hval,?_⟩
  intro μ
  exact (UnaryCarrier.Proof.ground_close_value (u 0) μ).trans hval.symm
end LogicLineages.OrdinalComparison.Source.UnitScalarEvaluationCode.Proof
