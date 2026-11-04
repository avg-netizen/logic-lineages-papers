module
public import LogicLineages.OrdinalComparison.ParametricRestrictedSourceEvaluatorTargets
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteAssignmentProof
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentCalibrationProof
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentSemanticProof
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeCalibrationProof
public import LogicLineages.OrdinalComparison.ParametricSourceEraserClosureProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Proof

open SourceGroundComponentEnvironment ParametricSourceEraser

theorem typedCalibration : Targets.TypedCalibration := by
  intro H i Γ t xs hΓ ht hlen
  obtain ⟨v, hv, hfree⟩ :=
    SourceRestrictedAssignmentFinite.Proof.actualAssignment Γ .ground t hΓ ht
  have hcodes := SourceMachineQueryCode.Proof.ground_codes Γ hΓ
  have hcheck := (SyntaxCode.Proof.typedCheckExact Γ .ground
    (SyntaxCode.encodeTerm t)).2 ⟨t, rfl⟩
  rw [hcodes] at hcheck
  have hassignment := DefaultSourceAssignment.Proof.assignmentCorrect Γ .ground t
  rw [hcodes, hv, Option.map_some] at hassignment
  have hslot : (OrdinalSyntax.vectorCode v)[0]? = some (OrdinalSyntax.typedCode (v 0)) := by
    simp [OrdinalSyntax.vectorCode]
  let result := ParametricOmegaFreeEvaluator.evaluate H i (environment xs)
    (OrdinalSyntax.typedCode (v 0))
  have heval : evaluate H i Γ.length (SyntaxCode.encodeTerm t) xs = some result := by
    simp only [evaluate, if_pos (And.intro hlen hcheck), hassignment,
      Option.bind_some, hslot]
    rfl
  have hdenote := ParametricOmegaFreeEvaluator.Proof.typedComponentCalibration Γ (v 0)
    H i (environment xs) (rawValuation xs) (hfree 0)
    (SourceGroundComponentEnvironment.Proof.typedLookup Γ xs hΓ hlen)
  have hscalar : Scalar (fun n => H (i, n)) (fun c => (rawValuation xs c : Ordinal)) t result :=
    ⟨v, hv, hdenote.symm⟩
  refine ⟨⟨result, heval⟩, ?_⟩
  intro r
  constructor
  · intro hr
    have he : result = r := Option.some.inj (heval.symm.trans hr)
    rw [← he]
    exact hscalar
  · intro hr
    have he : result = r := ParametricSourceEraser.Proof.scalar_unique
      (fun n => H (i, n)) (fun c => (rawValuation xs c : Ordinal)) t result r hscalar hr
    rw [← he]
    exact heval

end LogicLineages.OrdinalComparison.Source.ParametricRestrictedSourceEvaluator.Proof
