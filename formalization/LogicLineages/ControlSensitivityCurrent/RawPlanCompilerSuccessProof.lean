module
public import LogicLineages.ControlSensitivityCurrent.RawPlanCompilerTypedProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan GroundEquivalence

private theorem typed_ground_input (Γ : List Ty) (c : Code)
    (hc : c.1 = Γ.map SyntaxCode.typeCode) (ht : c.2.2.2 = 0) (hv : valid c = true) :
    ∃ d : Input Γ .ground, encode ⟨Γ,.ground,d⟩ = c := by
  obtain ⟨⟨Θ,τ,d⟩,hd⟩ := (valid_iff c).mp hv
  subst c
  have hΓ : Θ = Γ := by
    have h := congrArg (List.map SyntaxCode.decodeType) hc
    simpa only [encode, decode_types] using h
  have hτ : τ = Ty.ground := RawValidator.type_code_injective ht
  cases hΓ
  cases hτ
  exact ⟨d,rfl⟩

private theorem rename_input_valid (context table : List Nat) (c out : Code)
    (h : CheckedRenaming.rename context table c = some out) : valid c = true := by
  obtain ⟨Γ,Θ,τ,r,d,hc,_⟩ := CheckedRenaming.success_reconstruction context table c out h
  rw [← hc]
  exact typedAccepted _

private theorem equation_step_inputs (Γ : List Ty) (r : Result Γ) (a b : Code) (out : State)
    (h : compileStep (.inl (a,b)) (Γ.map SyntaxCode.typeCode, encodeResult r) = some out) :
    ∃ p q : Input Γ .ground, encode ⟨Γ,.ground,p⟩ = a ∧ encode ⟨Γ,.ground,q⟩ = b := by
  cases hg : equationGuard (Γ.map SyntaxCode.typeCode) a b with
  | false => simp [compileStep, encodeResult, hg] at h
  | true =>
      simp only [compileStep, encodeResult, hg, Bool.not_true, Bool.false_eq_true, ite_false] at h
      let context := r.context.map SyntaxCode.typeCode
      let table := Operations.renamingCode r.embedding
      change ((CheckedRenaming.rename context table a).bind fun a' =>
        (CheckedRenaming.rename context table b).bind fun b' =>
          some (Γ.map SyntaxCode.typeCode, context, table,
            (a',b') :: RawPrimitiveGateTargets.encodeForest r.forest)) = some out at h
      obtain ⟨a',ha,h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b',hb,_⟩ := Option.bind_eq_some_iff.mp h
      simp only [equationGuard, decide_eq_true_eq] at hg
      obtain ⟨p,hp⟩ := typed_ground_input Γ a hg.1 hg.2.2.1 (rename_input_valid _ _ _ a' ha)
      obtain ⟨q,hq⟩ := typed_ground_input Γ b hg.2.1 hg.2.2.2 (rename_input_valid _ _ _ b' hb)
      exact ⟨p,q,hp,hq⟩

private theorem gate_step_input (Γ : List Ty) (r : Result Γ) (raw : PrimitiveGate.GateCode) (out : State)
    (h : compileStep (.inr (.inl raw)) (Γ.map SyntaxCode.typeCode, encodeResult r) = some out) :
    ∃ g : PrimitiveLowering.Gate Γ, PrimitiveGate.encodeGate g = raw := by
  apply (PrimitiveGate.gate_exactness Γ raw).mp
  cases hg : PrimitiveGate.gateGuard (Γ.map SyntaxCode.typeCode) raw with
  | false => simp [compileStep, encodeResult, hg] at h
  | true => rfl

private theorem result_of_encoding {Γ : List Ty} {code : List Instruction} {out : State}
    (h : runState (Γ.map SyntaxCode.typeCode) code = some out)
    (q : Plan Γ) (he : encodePlan q = code) :
    out = (Γ.map SyntaxCode.typeCode, encodeResult (compile q)) := by
  have ht := typed_exactness Γ q
  rw [he, h] at ht
  exact Option.some.inj ht

theorem run_state_reconstruction (Γ : List Ty) (code : List Instruction) (out : State)
    (h : runState (Γ.map SyntaxCode.typeCode) code = some out) :
    ∃ q : Plan Γ, encodePlan q = code ∧ out = (Γ.map SyntaxCode.typeCode, encodeResult (compile q)) := by
  induction code generalizing Γ out with
  | nil => exact ⟨.done, rfl, result_of_encoding h .done rfl⟩
  | cons i code ih =>
      have hstep := h
      rw [run_state_cons] at hstep
      obtain ⟨tail,hTail,hStep⟩ := Option.bind_eq_some_iff.mp hstep
      rcases i with ⟨a,b⟩ | (raw | unit)
      · obtain ⟨q,hq,he⟩ := ih Γ tail hTail
        subst tail
        obtain ⟨p₁,p₂,h₁,h₂⟩ := equation_step_inputs Γ (compile q) a b out hStep
        have he : encodePlan (.equation p₁ p₂ q) = .inl (a,b) :: code := by
          simp [encodePlan, h₁, h₂, hq]
        exact ⟨.equation p₁ p₂ q, he, result_of_encoding h _ he⟩
      · obtain ⟨q,hq,he⟩ := ih Γ tail hTail
        subst tail
        obtain ⟨g,hg⟩ := gate_step_input Γ (compile q) raw out hStep
        have he : encodePlan (.gate g q) = .inr (.inl raw) :: code := by
          simp [encodePlan, hg, hq]
        exact ⟨.gate g q, he, result_of_encoding h _ he⟩
      · cases unit
        obtain ⟨q,hq,_⟩ := ih (.ground :: Γ) tail hTail
        have he : encodePlan (.existsGround q) = .inr (.inr PUnit.unit) :: code := by
          simp [encodePlan, hq]
        exact ⟨.existsGround q, he, result_of_encoding h _ he⟩

theorem success_reconstruction : RawPlanCompilerTargets.SuccessReconstruction := by
  intro context code out h
  obtain ⟨state, hstate, hproj⟩ := Option.map_eq_some_iff.mp h
  let Γ := context.map SyntaxCode.decodeType
  have hc : Γ.map SyntaxCode.typeCode = context := encode_types context
  obtain ⟨q, hq, he⟩ := run_state_reconstruction Γ code state (hc.symm ▸ hstate)
  exact ⟨Γ,q,hc,hq,hproj.symm.trans (congrArg Prod.snd he)⟩

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
