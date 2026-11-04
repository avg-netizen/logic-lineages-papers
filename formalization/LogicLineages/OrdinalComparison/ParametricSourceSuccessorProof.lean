module
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDenotationProof
public import LogicLineages.OrdinalComparison.ParametricCoefficientOneProof
public import LogicLineages.ComputabilityKnowledge.WWOmegaFiniteCalibrationProof
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.Proof
open LogicLineages.ComputabilityKnowledge
open WWOrdinalTermSemantics

theorem probe_assignment (Γ : List Ty) (x : Variable Γ .ground) :
    AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy (successorProbe x) =
      some (fun _ => .collapse .one (.add .one (.var ⟨.ground,x,0⟩))) := by
  simp only [successorProbe,AdmissibleAssignment.assignment]
  apply congrArg Option.some
  funext i
  have hi : i=0 := Fin.eq_zero i
  subst i
  simp [AdmissibleAssignment.application,AdmissibleAssignment.box,
    AdmissibleAssignment.boxTail,ordinalBoxPositive,ordinalVectorAt,Ty.level]

private theorem probe_denotation (G : Nat → Nat) (hm : StrictMono G) (hi : ∀ n,n ≤ G n)
    (Γ : List Ty) (x : Variable Γ .ground) (ρ : OrdinalComponent Γ → Nat) :
    denoteWith G (fun c => ((ρ c+1 : Nat) : Ordinal))
      (.collapse .one (.add .one (.var ⟨.ground,x,0⟩))) =
      ((G (ρ ⟨.ground,x,0⟩+4)+1 : Nat) : Ordinal) := by
  let n := ρ ⟨.ground,x,0⟩
  change (ParametricActualCollapse.collapseWith G
    (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
      (ordinalNaturalSum 1 ((n+1 : Nat) : Ordinal))) : Ordinal) = _
  have hs : ordinalNaturalSum 1 ((n+1 : Nat) : Ordinal) = ((n+2 : Nat) : Ordinal) := by
    simpa only [Nat.cast_one,Nat.add_comm 1 (n+1),Nat.add_assoc] using
      WWOrdinalTermSemanticsProof.naturalSum_finite 1 (n+1)
  rw [hs]
  have hp := WWOmegaFiniteCalibrationProof.productCalibration 1
  simp only [Nat.cast_one,mul_one] at hp
  rw [hp]
  have ha := WWOmegaFiniteCalibrationProof.sumCalibration 1 (n+2)
  simp only [Nat.cast_one,mul_one] at ha
  rw [ha]
  have hc := ParametricCoefficientOne.Proof.genericCoefficientOne G hm hi (n+2)
  change ParametricActualCollapse.collapseWith G (Ordinal.omega0+((n+2 : Nat) : Ordinal)) =
    G (n+2+2)+1 at hc
  rw [hc]

theorem genericSourceGraph : Targets.GenericSourceGraph := by
  intro G hm hi Γ x
  refine ⟨probe_assignment Γ x,?_⟩
  intro ρ y
  constructor
  · rintro ⟨v,hv,hd⟩
    rw [probe_assignment] at hv
    have he := Option.some.inj hv
    subst v
    rw [probe_denotation G hm hi Γ x ρ] at hd
    have hn : G (ρ ⟨.ground,x,0⟩+4)+1 = y+1 := by exact_mod_cast hd
    omega
  · intro hy
    refine ⟨_,probe_assignment Γ x,?_⟩
    rw [probe_denotation G hm hi Γ x ρ,hy]

theorem actualGammaGraph : Targets.ActualGammaGraph := by
  intro b Γ x ρ y
  have h := ParametricCoefficientOne.Proof.actualGammaCoefficientOne b
  exact (genericSourceGraph _ h.1 h.2.1 Γ x).2 ρ y
end LogicLineages.OrdinalComparison.Source.ParametricSourceSuccessor.Proof
