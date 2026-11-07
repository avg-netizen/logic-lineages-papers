module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationProof
open Source GammaGuardCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

theorem actualGammaPrimitive : GammaGuardCalibrationTargets.ActualGammaPrimitive := by
  have he : Primrec (fun q : ContextUniform.Object => Encodable.encode q.1) :=
    Primrec.encode.comp Primrec.fst
  exact Primrec.option_getD.comp
    ((Primrec.option_map₁ he).comp JointGammaProgramsDecoderProof.objectDecoderPrimitive)
    (Primrec.const 0)

theorem actualGammaProgram : GammaGuardCalibrationTargets.ActualGammaProgram := by
  apply Proof.allPrimitiveFunctions 1 gammaValue
  exact actualGammaPrimitive.comp
    (Primrec.vector_get.comp Primrec.id (Primrec.const (0 : Fin 1)))

theorem actualValidityEvaluation : GammaGuardCalibrationTargets.ActualValidityEvaluation := by
  intro p v
  change evaluate p _ = _
  congr 1

theorem actualValidityCalibration : GammaGuardCalibrationTargets.ActualValidityCalibration := by
  intro p hp v
  rw [actualValidityEvaluation,hp]
  rfl

theorem actualGuardRange : GammaGuardCalibrationTargets.ActualGuardRange := by
  intro v
  have hb (b : Bool) : b.toNat = 0 ∨ b.toNat = 1 := by cases b <;> simp
  cases hx : Encodable.decode (α := ContextUniform.Object) (v.get 0) with
  | none => simp only [JointGammaDomain.guardValue,hx]; exact Or.inl trivial
  | some x =>
    cases hu : Encodable.decode (α := ContextUniform.Object) (v.get 1) with
    | none => simp only [JointGammaDomain.guardValue,hx,hu]; exact Or.inl trivial
    | some u => simpa only [JointGammaDomain.guardValue,hx,hu] using hb (decide (x.1 = u.1))

theorem actualObjectValidity : GammaGuardCalibrationTargets.ActualObjectValidity := by
  intro x
  cases hx : Encodable.decode (α := ContextUniform.Object) x <;>
    simp [objectValid,JointGammaDomain.guardValue,hx]

theorem actualGammaDecoded : GammaGuardCalibrationTargets.ActualGammaDecoded := by
  intro x obj hx
  simp [gammaCode,hx]

theorem actualGuardCalibration : GammaGuardCalibrationTargets.ActualGuardCalibration := by
  intro x u
  rw [JointGammaDomainProof.actualGuardCalibration.1]
  constructor
  · rintro ⟨Gamma,a,b,hx,hu⟩
    refine ⟨(actualObjectValidity x).mpr ⟨(Gamma,a),hx⟩,
      (actualObjectValidity u).mpr ⟨(Gamma,b),hu⟩,?_⟩
    rw [actualGammaDecoded x (Gamma,a) hx,actualGammaDecoded u (Gamma,b) hu]
  · rintro ⟨hx,hu,he⟩
    obtain ⟨⟨Gamma,a⟩,hxd⟩ := (actualObjectValidity x).mp hx
    obtain ⟨⟨Delta,b⟩,hud⟩ := (actualObjectValidity u).mp hu
    rw [actualGammaDecoded x (Gamma,a) hxd,actualGammaDecoded u (Delta,b) hud] at he
    have hgd : Gamma = Delta := Encodable.encode_injective he
    subst Delta
    exact ⟨Gamma,a,b,hxd,hud⟩

theorem actualTypedValid : GammaGuardCalibrationTargets.ActualTypedValid := by
  intro n arity c t x h
  obtain ⟨Gamma,value,hx,_⟩ := (JointGammaTypedProof.calibration n arity c t x).mp h
  exact (actualObjectValidity x).mpr ⟨(Gamma,value),hx⟩

theorem actualPositiveGamma : GammaGuardCalibrationTargets.ActualPositiveGamma := by
  intro n arity c x y k h
  cases hx : Encodable.decode (α := ContextUniform.Object) x with
  | none => simp [ContextUniform.positiveValue,hx] at h
  | some source =>
    cases hy : Encodable.decode (α := ContextUniform.Object) y with
    | none => simp [ContextUniform.positiveValue,hx,hy] at h
    | some target =>
      have he : source.1 = target.1 := by
        by_contra hn
        simp [ContextUniform.positiveValue,hx,hy,hn] at h
      rw [actualGammaDecoded x source hx,actualGammaDecoded y target hy,he]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationProof
