module
public import LogicLineages.ControlSensitivityCurrent.CurrentCompilerTargets
public import LogicLineages.ControlSensitivityCurrent.RawPlanComparisonProof
public import LogicLineages.ControlSensitivityCurrent.RawInputCompilerSuccessProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentCompiler

open LogicLineages.OrdinalComparison.Source
open RawSourceDAG
open InputCompiler (InputCode encodeInput)
open PlanComparison (OutputCode compileComparisons)

theorem ground_context_code (n : Nat) :
    (List.replicate n Ty.ground).map SyntaxCode.typeCode = List.replicate n 0 := by
  simp [SyntaxCode.typeCode]

theorem run_typed (n : Nat) (q : InputNormalization.Input (List.replicate n Ty.ground) 0) :
    run n (encodeInput q) = some (expected q) := by
  let p := InputNormalization.normalize .nil q
  have hi := InputCompiler.typed_exactness (List.replicate n Ty.ground) q
  have hp := PlanComparison.typed_exactness (List.replicate n Ty.ground) (BooleanCompiler.lower p)
  rw [ground_context_code] at hi hp
  simp only [run, hi, Option.bind_some, hp, expected, BooleanCompiler.strictPair, BooleanCompiler.weakPair, p]

theorem literal_outputs : CurrentCompilerTargets.LiteralOutputs := by
  constructor
  · intro n q
    exact ⟨run_typed n q, by simp [compile, run_typed]⟩
  · intro s
    have h := run_typed s.variables s.matrix.toInput
    simp only [compile, h, Option.getD_some, expected, SourceAST.Formula.toProgram]

theorem successful_input (n : Nat) (code : InputCode) (out : OutputCode)
    (h : run n code = some out) :
    ∃ q : InputNormalization.Input (List.replicate n Ty.ground) 0, encodeInput q = code ∧ out = expected q := by
  obtain ⟨plan, hp, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Γ,q,hc,hq,_⟩ := InputCompiler.success_reconstruction _ _ _ hp
  have hΓ : Γ = List.replicate n Ty.ground := by
    have he := congrArg (List.map SyntaxCode.decodeType) (hc.trans (ground_context_code n).symm)
    simpa only [decode_types] using he
  subst Γ
  have ht := run_typed n q
  rw [hq,h] at ht
  exact ⟨q,hq,Option.some.inj ht⟩

theorem valid_codes : CurrentCompilerTargets.ValidCodes := by
  refine ⟨successful_input, ?_⟩
  intro n code
  constructor
  · intro h
    rintro ⟨q,rfl⟩
    rw [run_typed] at h
    cases h
  · intro h
    cases hs : run n code with
    | none => rfl
    | some out =>
      obtain ⟨q,hq,_⟩ := successful_input n code out hs
      exact (h ⟨q,hq⟩).elim

end LogicLineages.ControlSensitivityCurrent.CurrentCompiler
