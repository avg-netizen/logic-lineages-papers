module
public import LogicLineages.ControlSensitivityCurrent.PolicyObservationTargets
public import LogicLineages.ControlSensitivityCurrent.GenericScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.PolicyObservation
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ParametricSourceSuccessor
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem expressionNaturality : PolicyObservationTargets.ExpressionNaturality := by
  intro f Γ Δ r ν μ h t
  induction t with
  | var c => rcases c with ⟨τ,x,j⟩; exact h τ x j
  | zero | one | omega => rfl
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    simp only [ordinalExpressionRename,substitute,denoteWith] at *
    rw [ha,hb]

private theorem scalar_eq (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (ρ : OrdinalComponent Γ → Nat) (t : OriginalTerm Γ .ground)
    (v : OrdinalVector Γ 0) (n : Nat)
    (hv : AdmissibleAssignment.assignment p t = some v)
    (hn : denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal)) :
    PolicyCollision.rawScalar p f ρ t = n := by
  unfold PolicyCollision.rawScalar
  rw [hv]
  change OriginalDomain.finiteValue (denoteWith f _ (v 0)) = n
  rw [hn]
  exact OriginalDomain.originalFiniteValueCalibration n

theorem sourceNaturality : PolicyObservationTargets.SourceNaturality := by
  intro p f Γ Δ r ρ σ h t
  obtain ⟨v,hv,n,hp,hn,hu⟩ := GenericScalar.actualSourceTotality p f Γ ρ t
  have ht := SourceRenaming.Proof.assignmentNaturality Γ Δ .ground r p t
  rw [hv] at ht
  have he := expressionNaturality f Γ Δ r
    (fun c => ((ρ c+1 : Nat) : Ordinal)) (fun c => ((σ c+1 : Nat) : Ordinal))
    (fun τ x j => by rw [h τ x j]) (v 0)
  have hv' : AdmissibleAssignment.assignment p (t.rename r) = some (SourceRenaming.renameVector r v) := ht
  have hn' : denoteWith f (fun c => ((σ c+1 : Nat) : Ordinal)) (SourceRenaming.renameVector r v 0) = (n : Ordinal) := he.trans hn
  exact (scalar_eq p f σ _ _ n hv' hn').trans (scalar_eq p f ρ t v n hv hn).symm

theorem observationCalibration : PolicyObservationTargets.ObservationCalibration := by
  intro p f Γ ρ t
  obtain ⟨v,hv,n,hp,hn,hu⟩ := GenericScalar.actualSourceTotality p f Γ ρ t
  have hr := scalar_eq p f ρ t v n hv hn
  rw [hr]
  have he : n-1+1=n := by omega
  refine ⟨he,v,hv,?_⟩
  rw [he]
  exact hn

theorem equationCalibration : PolicyObservationTargets.EquationCalibration := by
  intro p f Γ ρ a b
  obtain ⟨va,hva,x,hx,hex,hux⟩ := GenericScalar.actualSourceTotality p f Γ ρ a
  obtain ⟨vb,hvb,y,hy,hey,huy⟩ := GenericScalar.actualSourceTotality p f Γ ρ b
  rw [scalar_eq p f ρ a va x hva hex,scalar_eq p f ρ b vb y hvb hey]
  constructor
  · rintro ⟨wa,wb,ha,hb,he⟩
    rw [hva] at ha
    rw [hvb] at hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    rw [hex,hey] at he
    exact_mod_cast he
  · intro h
    refine ⟨va,vb,hva,hvb,?_⟩
    rw [hex,hey,h]
#audit_namespace LogicLineages.ControlSensitivityCurrent.PolicyObservation
end LogicLineages.ControlSensitivityCurrent.PolicyObservation
