module
public import LogicLineages.PermittedControl.SelectedAggregationFoldProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedAggregation.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open SelectedFunctionalDetector.Proof
open OrdinalComparison.ParametricActualCollapse
open Vendor.R1

private theorem omega_one : ordinalNaturalProduct Ordinal.omega0 1 = Ordinal.omega0 := by
  let w : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  let o : NONote := ⟨1, ONote.nf_one⟩
  have h := naturalProductDenotation w o
  have hw : w.1.repr = Ordinal.omega0 := by simp [w,ONote.repr]
  have ho : o.1.repr = 1 := by simp [o,ONote.repr_one]
  have hp : (naturalProduct w o).1 = w.1 := by
    change rawNaturalProduct (.oadd 1 1 .zero) (.oadd .zero 1 .zero) = .oadd 1 1 .zero
    have hz (x : ONote) : rawNaturalSum x .zero = x := by
      cases x <;> rw [rawNaturalSum] <;> simp
    simp only [rawNaturalProduct,rawMonomialProduct,hz]
    congr 2
  rw [hp,hw,ho] at h
  exact h.symm

theorem constant_value {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (r : OriginalTerm Γ .ground) :
    groundValue ctrl policy ρ (ParametricLiteralWeakWrapper.constantApply r)=
      collapseWith ctrl (Ordinal.omega0+((5+groundValue ctrl policy ρ r : Nat) : Ordinal)) := by
  have h := eraser_value ctrl K hc policy ρ (.zeroC : OriginalTerm Γ .ground) r
  rw [zero_value ctrl K hc policy ρ] at h
  convert h using 1 <;> congr 2 <;> omega

theorem identity_value {Γ} (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K)
    (policy : Policy) (ρ : AdmissibleSubstitution ctrl Γ) (l : OriginalTerm Γ .ground) :
    groundValue ctrl policy ρ (ParametricLiteralWeakWrapper.identityApply l)=
      collapseWith ctrl (Ordinal.omega0+((3+groundValue ctrl policy ρ l : Nat) : Ordinal)) := by
  obtain ⟨v,hv,hs,hpos⟩ := ground_facts ctrl K hc policy l ρ
  have hi := SelectedHardnessPairSyntaxProof.identity_assignment policy Γ
  have happ := SelectedHardnessCombinatorSyntaxProof.app_assignment policy _ l _ v hi hv
  have hthree : expressionValue ctrl ρ (SelectedHardnessPairSyntaxProof.identityVector Γ 0)=
      ((3 : Nat) : Ordinal) := by
    change ordinalNaturalSum (ordinalNaturalSum 1 1) 1=_
    have h2 := naturalSum_finite 1 1
    have h3 := naturalSum_finite 2 1
    simpa only [Nat.cast_one] using (congrArg (fun x => ordinalNaturalSum x 1) h2).trans h3
  have h := unary_app_value ctrl policy (valuation ctrl ρ)
    (SelectedHardnessPairSyntaxProof.identityVector Γ) v 3 _ hthree hs
  change _=(collapseWith ctrl (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
    ((3+groundValue ctrl policy ρ l : Nat) : Ordinal)) : Ordinal) at h
  rw [omega_one,actualNaturalSumFiniteRight] at h
  exact ground_of_assignment ctrl policy ρ _ _ _ happ h

 theorem actualWeakConversion : SelectedAggregationTargets.ActualWeakConversion := by
  intro ctrl K hc Γ policy ρ l r
  refine ⟨groundResult ctrl K hc policy ρ _,groundResult ctrl K hc policy ρ _,
    constant_value ctrl K hc policy ρ r,identity_value ctrl K hc policy ρ l,?_⟩
  rw [constant_value ctrl K hc policy ρ r,identity_value ctrl K hc policy ρ l]
  rw [ParametricCoefficientOne.Proof.genericCoefficientOne ctrl
    (selected_threshold_admissible ctrl K hc).1 (selectedInflation ctrl K hc),
    ParametricCoefficientOne.Proof.genericCoefficientOne ctrl
    (selected_threshold_admissible ctrl K hc).1 (selectedInflation ctrl K hc)]
  have hm := (selected_threshold_admissible ctrl K hc).1
  constructor
  · intro h
    have hh : 5+groundValue ctrl policy ρ r+2≤3+groundValue ctrl policy ρ l+2 :=
      hm.le_iff_le.mp (by omega)
    omega
  · intro h
    have hh := hm.monotone (show 5+groundValue ctrl policy ρ r+2≤
      3+groundValue ctrl policy ρ l+2 by omega)
    omega

 theorem aggregateWeakQuery : SelectedAggregationTargets.AggregateWeakQuery := by
  intro ctrl K hc Γ policy ρ es
  obtain ⟨_,_,hle,heq,hgap⟩ := aggregateAt ctrl K hc policy ρ es
  have hw := (actualWeakConversion ctrl K hc Γ policy ρ
    (SourceAggregateCompletion.aggregate es).1 (SourceAggregateCompletion.aggregate es).2).2.2.2.2
  constructor
  · constructor
    · intro h hh
      have he := heq.mpr hh
      omega
    · intro h
      have hg := hgap h
      omega
  · rw [hw]
    constructor
    · intro h hh
      have he := heq.mpr hh
      omega
    · exact hgap

 theorem selectedAggregation : SelectedAggregationTargets.SelectedAggregation :=
  ⟨sixEraserCollision,actualAggregation,actualWeakConversion,aggregateWeakQuery⟩
end LogicLineages.PermittedControl.SelectedAggregation.Proof
