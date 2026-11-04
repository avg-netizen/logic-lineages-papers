module
public import LogicLineages.OrdinalComparison.ParametricLiteralWeakWrapperTargets
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceScalarProof
public import LogicLineages.OrdinalComparison.ParametricSourceAdditionAtomicProof
public import LogicLineages.OrdinalComparison.ParametricFiniteCollapseArgumentProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.Source.ParametricLiteralWeakWrapper.Proof

open ParametricSourceSuccessor ParametricSourceEraser

theorem exactAssignment : Targets.ExactAssignment := by
  intro Γ t v hv
  exact ⟨GroundEquivalence.Proof.identity_application t v hv,
    GroundEquivalence.Proof.constant_application t v hv⟩

private theorem collapse_coefficient (G : Nat → Nat) {Γ : List Ty}
    (ν : OrdinalComponent Γ → Ordinal) (a : OrdinalExpression Γ) (n : Nat)
    (ha : denoteWith G ν a = (n : Ordinal)) :
    denoteWith G ν (.collapse .one a) =
      (ParametricCoefficientOne.coefficientOne G n : Ordinal) := by
  have hc := ParametricFiniteCollapseArgument.Proof.denotationCalibration
    (OrdinalComponent Γ) G ν .one a 1 n (by simp [denoteWith]) ha
  simpa only [ParametricFinitePairCollapse.value, ParametricFinitePairCollapse.ordinal,
    Nat.cast_one, mul_one, ParametricCoefficientOne.coefficientOne] using hc

theorem finiteCoefficientCalibration : Targets.FiniteCoefficientCalibration := by
  intro G Γ ν t x hx
  obtain ⟨v, hv, hx⟩ := hx
  have ha := exactAssignment Γ t v hv
  have h1 : denoteWith G ν (.one : OrdinalExpression Γ) = ((1 : Nat) : Ordinal) := by
    simp [denoteWith]
  have h2 := ParametricSourceAddition.Proof.add_value G ν .one .one 1 1 h1 h1
  have h3 : denoteWith G ν (three : OrdinalExpression Γ) = ((3 : Nat) : Ordinal) :=
    ParametricSourceAddition.Proof.add_value G ν _ .one 2 1 h2 h1
  have h4 := ParametricSourceAddition.Proof.add_value G ν _ _ 2 2 h2 h2
  have h5 : denoteWith G ν (five : OrdinalExpression Γ) = ((5 : Nat) : Ordinal) :=
    ParametricSourceAddition.Proof.add_value G ν _ .one 4 1 h4 h1
  have hthree : denoteWith G ν (.add three (v 0)) = ((x + 3 : Nat) : Ordinal) := by
    simpa only [Nat.add_comm] using
      ParametricSourceAddition.Proof.add_value G ν three (v 0) 3 x h3 hx
  have hfive : denoteWith G ν (.add five (v 0)) = ((x + 5 : Nat) : Ordinal) := by
    simpa only [Nat.add_comm] using
      ParametricSourceAddition.Proof.add_value G ν five (v 0) 5 x h5 hx
  constructor
  · exact ⟨(fun _ => .collapse .one (.add three (v 0))), ha.1,
      collapse_coefficient G ν _ _ hthree⟩
  · exact ⟨(fun _ => .collapse .one (.add five (v 0))), ha.2,
      collapse_coefficient G ν _ _ hfive⟩

theorem controlValueCalibration : Targets.ControlValueCalibration := by
  intro G hm hi Γ ν t x hx
  have h := finiteCoefficientCalibration G Γ ν t x hx
  rw [ParametricCoefficientOne.Proof.genericCoefficientOne G hm hi (x + 3),
    ParametricCoefficientOne.Proof.genericCoefficientOne G hm hi (x + 5)] at h
  simpa only [Nat.add_assoc] using h

end LogicLineages.OrdinalComparison.Source.ParametricLiteralWeakWrapper.Proof
