module
public import LogicLineages.PermittedControl.SelectedDetectorPadProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorAlgebraProof
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
open OrdinalComparison Source Source.AdmissibleSum Source.AdmissibleAssignment SelectedSourceDomain
open Source.FunctionalDetector (unary shiftTwo alignedLeft alignedRight)

theorem alignment (ctrl : Nat → Nat) (K : Nat) (hc : SelectedWithThreshold ctrl K) (pol : Policy) (Γ : List Ty) (a b : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution ctrl Γ) :
    HeadEqual ctrl pol ρ a b ↔ ∃z w : Nat,
      VectorEqual ctrl pol (extend ctrl ρ z w) (alignedLeft a) (alignedRight b) := by
  obtain ⟨av,na,ha,hna,_⟩ := source_facts ctrl K hc pol a ρ
  obtain ⟨bv,nb,hb,hnb,_⟩ := source_facts ctrl K hc pol b ρ
  let va := SourceRenaming.renameVector (shiftTwo Γ) av
  let vb := SourceRenaming.renameVector (shiftTwo Γ) bv
  let vz : OrdinalVector (.ground::.ground::Γ) 0 := fun j => .var ⟨.ground,.here,j⟩
  let vw : OrdinalVector (.ground::.ground::Γ) 0 := fun j => .var ⟨.ground,.there .here,j⟩
  have ha' : assignment pol (a.rename (shiftTwo Γ))=some va := by
    rw [SourceRenaming.Proof.assignmentNaturality,ha]
    rfl
  have hb' : assignment pol (b.rename (shiftTwo Γ))=some vb := by
    rw [SourceRenaming.Proof.assignmentNaturality,hb]
    rfl
  have hal : assignment pol (alignedLeft a)=some (padVector pol va vz) :=
    pad_assignment pol _ _ _ _ ha' rfl
  have hbr : assignment pol (alignedRight b)=some (padVector pol vb vw) :=
    pad_assignment pol _ _ _ _ hb' rfl
  have hv (z w : Nat) (i : Fin 2) :
      expressionValue ctrl (extend ctrl ρ z w) (va i)=expressionValue ctrl ρ (av i) := renamed_value ctrl ρ z w _
  have hw (z w : Nat) (i : Fin 2) :
      expressionValue ctrl (extend ctrl ρ z w) (vb i)=expressionValue ctrl ρ (bv i) := renamed_value ctrl ρ z w _
  have hz (z w : Nat) : expressionValue ctrl (extend ctrl ρ z w) (vz 0)=((z+1:Nat):Ordinal) :=
    extension_here ctrl _ _
  have hww (z w : Nat) : expressionValue ctrl (extend ctrl ρ z w) (vw 0)=((w+1:Nat):Ordinal) :=
    by
      change valuation ctrl (groundExtension ctrl ρ w) ⟨.ground,.here,0⟩=_
      exact extension_here ctrl ρ w
  rw [headEqual_iff ctrl pol ρ a b av bv ha hb]
  constructor
  · intro he
    refine ⟨5*nb,5*na,(vectorEqual_iff ctrl pol _ _ _ _ _ hal hbr).mpr ?_⟩
    intro j
    have hj : j=0 ∨ j=1 := by
      have h := j.isLt
      by_cases he : j.val=0
      · left; exact Fin.ext he
      · right; apply Fin.ext; simp only [Fin.val_one]; omega
    rcases hj with hj | hj <;> subst j
    · have hl := pad_scalar ctrl pol (valuation ctrl (extend ctrl ρ (5*nb) (5*na))) va vz na (5*nb+1)
        ((hv _ _ 0).trans hna) (hz _ _)
      have hr := pad_scalar ctrl pol (valuation ctrl (extend ctrl ρ (5*nb) (5*na))) vb vw nb (5*na+1)
        ((hw _ _ 0).trans hnb) (hww _ _)
      change ParametricSourceSuccessor.denoteWith ctrl _ _=ParametricSourceSuccessor.denoteWith ctrl _ _
      rw [hl,hr]
      change (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (SelectedHardness.paddedHead (expressionValue ctrl (extend ctrl ρ (5*nb) (5*na)) (va 1))))
        ((5*na+4+(5*nb+1):Nat):Ordinal)):Ordinal)=
        (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
          (ordinalNaturalProduct Ordinal.omega0 (SelectedHardness.paddedHead (expressionValue ctrl (extend ctrl ρ (5*nb) (5*na)) (vb 1))))
          ((5*nb+4+(5*na+1):Nat):Ordinal)):Ordinal)
      rw [hv,hw,he]
      rw [show 5*na+4+(5*nb+1)=5*nb+4+(5*na+1) by omega]
    · change ParametricSourceSuccessor.denoteWith ctrl _ _=ParametricSourceSuccessor.denoteWith ctrl _ _
      rw [pad_head ctrl pol,pad_head ctrl pol]
      change SelectedHardness.paddedHead (expressionValue ctrl (extend ctrl ρ (5*nb) (5*na)) (va 1))=
        SelectedHardness.paddedHead (expressionValue ctrl (extend ctrl ρ (5*nb) (5*na)) (vb 1))
      rw [hv,hw,he]
  · rintro ⟨z,w,h⟩
    have hh := (vectorEqual_iff ctrl pol _ _ _ _ _ hal hbr).mp h 1
    change ParametricSourceSuccessor.denoteWith ctrl _ _=ParametricSourceSuccessor.denoteWith ctrl _ _ at hh
    rw [pad_head ctrl pol,pad_head ctrl pol] at hh
    change SelectedHardness.paddedHead (expressionValue ctrl (extend ctrl ρ z w) (va 1))=
      SelectedHardness.paddedHead (expressionValue ctrl (extend ctrl ρ z w) (vb 1)) at hh
    rw [hv,hw] at hh
    exact Source.FunctionalDetector.Proof.paddedHead_injective hh
end LogicLineages.PermittedControl.SelectedFunctionalDetector.Proof
