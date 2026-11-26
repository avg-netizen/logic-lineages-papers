module
public import LogicLineages.PermittedControl.StandardAggregationFoldProof
@[expose] public section
namespace LogicLineages.PermittedControl.StandardAggregation.Proof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain SelectedFunctionalDetector
open StandardFunctionalDetector.Proof
open SelectedAggregation
open StandardApplicationEraser.Proof (unary_app_value)
open OrdinalComparison.ParametricActualCollapse
open Vendor.R1
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

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

theorem constant_value {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (r : OriginalTerm Γ .ground) :
    groundValue Phi policy ρ (ParametricLiteralWeakWrapper.constantApply r)=
      collapseWith Phi (Ordinal.omega0+((5+groundValue Phi policy ρ r : Nat) : Ordinal)) := by
  have h := eraser_value  policy ρ (.zeroC : OriginalTerm Γ .ground) r
  rw [zero_value  policy ρ] at h
  rw [show 3*1+groundValue Phi policy ρ r+2=5+groundValue Phi policy ρ r by omega] at h
  exact h

theorem identity_value {Γ} 
    (policy : Policy) (ρ : AdmissibleSubstitution Phi Γ) (l : OriginalTerm Γ .ground) :
    groundValue Phi policy ρ (ParametricLiteralWeakWrapper.identityApply l)=
      collapseWith Phi (Ordinal.omega0+((3+groundValue Phi policy ρ l : Nat) : Ordinal)) := by
  obtain ⟨v,hv,hs,hpos⟩ := ground_facts  policy l ρ
  have hi := SelectedHardnessPairSyntaxProof.identity_assignment policy Γ
  have happ := SelectedHardnessCombinatorSyntaxProof.app_assignment policy _ l _ v hi hv
  have hthree : expressionValue Phi ρ (SelectedHardnessPairSyntaxProof.identityVector Γ 0)=
      ((3 : Nat) : Ordinal) := by
    change ordinalNaturalSum (ordinalNaturalSum 1 1) 1=_
    have h2 : ordinalNaturalSum (1 : Ordinal) 1=(2 : Ordinal) := by
      simpa using naturalSum_finite 1 1
    have h3 : ordinalNaturalSum (2 : Ordinal) 1=((3 : Nat) : Ordinal) := by
      simpa using naturalSum_finite 2 1
    exact (congrArg (fun x => ordinalNaturalSum x 1) h2).trans h3
  have h := unary_app_value Phi policy (valuation Phi ρ)
    (SelectedHardnessPairSyntaxProof.identityVector Γ) v 3 _ hthree hs
  change _=(collapseWith Phi (ordinalNaturalSum (ordinalNaturalProduct Ordinal.omega0 1)
    ((3+groundValue Phi policy ρ l : Nat) : Ordinal)) : Ordinal) at h
  rw [omega_one,actualNaturalSumFiniteRight] at h
  exact ground_of_assignment Phi policy ρ _ _ _ happ h

 theorem actualWeakConversion : StandardAggregation.ActualWeakConversion := by
  intro Γ policy ρ l r
  refine ⟨groundResult  policy ρ _,groundResult  policy ρ _,
    constant_value  policy ρ r,identity_value  policy ρ l,?_⟩
  rw [constant_value  policy ρ r,identity_value  policy ρ l]
  change ParametricCoefficientOne.coefficientOne Phi (5+groundValue Phi policy ρ r)≤
    ParametricCoefficientOne.coefficientOne Phi (3+groundValue Phi policy ρ l) ↔ _
  rw [ParametricCoefficientOne.Proof.genericCoefficientOne Phi
    Phi_strictMono (selectedInflation ),
    ParametricCoefficientOne.Proof.genericCoefficientOne Phi
    Phi_strictMono (selectedInflation )]
  have hm := Phi_strictMono
  constructor
  · intro h
    have hh : 5+groundValue Phi policy ρ r+2≤3+groundValue Phi policy ρ l+2 :=
      hm.le_iff_le.mp (by omega)
    omega
  · intro h
    have hh := hm.monotone (show 5+groundValue Phi policy ρ r+2≤
      3+groundValue Phi policy ρ l+2 by omega)
    omega

 theorem aggregateWeakQuery : StandardAggregation.AggregateWeakQuery := by
  intro Γ policy ρ es
  obtain ⟨_,_,hle,heq,hgap⟩ := aggregateAt  policy ρ es
  have hw := (actualWeakConversion  Γ policy ρ
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

 theorem selectedAggregation : StandardAggregation.StandardAggregation :=
  ⟨sixEraserCollision,actualAggregation,actualWeakConversion,aggregateWeakQuery⟩
end LogicLineages.PermittedControl.StandardAggregation.Proof
