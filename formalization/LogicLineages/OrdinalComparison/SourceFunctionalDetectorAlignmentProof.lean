module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorFactsProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorAlgebraProof
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorCombinatorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
open OriginalDomain AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

def padVector {Γ} (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) : OrdinalVector Γ 1 :=
  application (σ:=.ground) (τ:=unary) OrdinalSyntax.defaultPolicy
    (AbsoluteObserver.Proof.unusedVector av) qv

theorem pad_assignment {Γ} (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hq : assignment OrdinalSyntax.defaultPolicy q=some qv) :
    assignment OrdinalSyntax.defaultPolicy (pad a q)=some (padVector av qv) :=
  AbsoluteObserver.Proof.app_assignment _ _ _ _ (AbsoluteObserver.Proof.unused_assignment a av ha) hq

theorem pad_head_expression {Γ} (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) :
    padVector av qv 1=unusedHead (av 1) := by
  change ordinalBoxPositive 0 (@ordinalVectorAt Γ 1 (AbsoluteObserver.Proof.unusedVector av))
    (@ordinalVectorAt Γ 0 qv) 1=_
  rw [ordinalBoxPositive]
  simp only [show ¬(1≤0) by omega,dite_false,ordinalVectorAt]
  simp [AbsoluteObserver.Proof.unusedVector,AbsoluteObserver.Proof.freePart,
    OrdinalSyntax.defaultPolicy,OrdinalSyntax.defaultShape,OrdinalSyntax.leftShape,
    AdmissibleSum.expand,unusedHead]

theorem pad_head {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) :
    denote ν (padVector av qv 1)=paddedHead (denote ν (av 1)) := by
  rw [pad_head_expression]
  rfl

theorem pad_scalar {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (av : OrdinalVector Γ 1) (qv : OrdinalVector Γ 0) (a0 q0 : Nat)
    (ha : denote ν (av 0)=(a0:Ordinal)) (hq : denote ν (qv 0)=(q0:Ordinal)) :
    denote ν (padVector av qv 0)=
      (actualCollapse (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (paddedHead (denote ν (av 1))))
        ((5*a0+4+q0:Nat):Ordinal)):Ordinal) := by
  have hh := pad_head_expression av qv
  have hs := AbsoluteObserver.Proof.unused_scalar (τ:=unary) ν av a0 ha
  have hs' : denote ν (AbsoluteObserver.Proof.unusedVector av 0)=((5*a0+4:Nat):Ordinal) := by
    change denote ν (AbsoluteObserver.Proof.unusedVector av 0)=((5*a0+4:Nat):Ordinal) at hs
    exact hs
  have he : padVector av qv 0= .collapse (unusedHead (av 1))
      (.add (AbsoluteObserver.Proof.unusedVector av 0) (qv 0)) := by
    change Term.collapse (padVector av qv 1)
      (.add (AbsoluteObserver.Proof.unusedVector av 0) (qv 0))=_
    rw [hh]
  rw [he]
  simp only [denote,hs',hq,naturalSum_finite]
  rfl

theorem headEqual_iff {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary)
    (av bv : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hb : assignment OrdinalSyntax.defaultPolicy b=some bv) :
    HeadEqual ρ a b ↔ expressionValue ρ (av 1)=expressionValue ρ (bv 1) := by
  constructor
  · rintro ⟨v,w,hv,hw,h⟩
    have he := Option.some.inj (ha.symm.trans hv)
    have hf := Option.some.inj (hb.symm.trans hw)
    cases he; cases hf
    exact h
  · exact fun h => ⟨av,bv,ha,hb,h⟩

theorem vectorEqual_iff {Γ} (ρ : AdmissibleSubstitution Γ) (a b : OriginalTerm Γ unary)
    (av bv : OrdinalVector Γ 1)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some av)
    (hb : assignment OrdinalSyntax.defaultPolicy b=some bv) :
    VectorEqual ρ a b ↔ ∀j, expressionValue ρ (av j)=expressionValue ρ (bv j) := by
  constructor
  · rintro ⟨v,w,hv,hw,h⟩
    have he := Option.some.inj (ha.symm.trans hv)
    have hf := Option.some.inj (hb.symm.trans hw)
    cases he; cases hf
    exact h
  · exact fun h => ⟨av,bv,ha,hb,h⟩

theorem alignment (Γ : List Ty) (a b : OriginalTerm Γ unary) (ρ : AdmissibleSubstitution Γ) :
    HeadEqual ρ a b ↔ ∃z w : Nat,
      VectorEqual (extend ρ z w) (alignedLeft a) (alignedRight b) := by
  obtain ⟨av,na,ha,hna,_⟩ := source_facts a ρ
  obtain ⟨bv,nb,hb,hnb,_⟩ := source_facts b ρ
  let va := SourceRenaming.renameVector (shiftTwo Γ) av
  let vb := SourceRenaming.renameVector (shiftTwo Γ) bv
  let vz : OrdinalVector (.ground::.ground::Γ) 0 := fun j => .var ⟨.ground,.here,j⟩
  let vw : OrdinalVector (.ground::.ground::Γ) 0 := fun j => .var ⟨.ground,.there .here,j⟩
  have ha' : assignment OrdinalSyntax.defaultPolicy (a.rename (shiftTwo Γ))=some va := by
    rw [SourceRenaming.Proof.assignmentNaturality,ha]
    rfl
  have hb' : assignment OrdinalSyntax.defaultPolicy (b.rename (shiftTwo Γ))=some vb := by
    rw [SourceRenaming.Proof.assignmentNaturality,hb]
    rfl
  have hal : assignment OrdinalSyntax.defaultPolicy (alignedLeft a)=some (padVector va vz) :=
    pad_assignment _ _ _ _ ha' rfl
  have hbr : assignment OrdinalSyntax.defaultPolicy (alignedRight b)=some (padVector vb vw) :=
    pad_assignment _ _ _ _ hb' rfl
  have hv (z w : Nat) (i : Fin 2) :
      expressionValue (extend ρ z w) (va i)=expressionValue ρ (av i) := renamed_value ρ z w _
  have hw (z w : Nat) (i : Fin 2) :
      expressionValue (extend ρ z w) (vb i)=expressionValue ρ (bv i) := renamed_value ρ z w _
  have hz (z w : Nat) : expressionValue (extend ρ z w) (vz 0)=((z+1:Nat):Ordinal) :=
    extension_here _ _
  have hww (z w : Nat) : expressionValue (extend ρ z w) (vw 0)=((w+1:Nat):Ordinal) :=
    by
      change valuation (groundExtension ρ w) ⟨.ground,.here,0⟩=_
      exact extension_here ρ w
  rw [headEqual_iff ρ a b av bv ha hb]
  constructor
  · intro he
    refine ⟨5*nb,5*na,(vectorEqual_iff _ _ _ _ _ hal hbr).mpr ?_⟩
    intro j
    have hj : j=0 ∨ j=1 := by
      have h := j.isLt
      by_cases he : j.val=0
      · left; exact Fin.ext he
      · right; apply Fin.ext; simp only [Fin.val_one]; omega
    rcases hj with hj | hj <;> subst j
    · have hl := pad_scalar (valuation (extend ρ (5*nb) (5*na))) va vz na (5*nb+1)
        ((hv _ _ 0).trans hna) (hz _ _)
      have hr := pad_scalar (valuation (extend ρ (5*nb) (5*na))) vb vw nb (5*na+1)
        ((hw _ _ 0).trans hnb) (hww _ _)
      change denote _ _=denote _ _
      rw [hl,hr]
      change (actualCollapse (ordinalNaturalSum
        (ordinalNaturalProduct Ordinal.omega0 (paddedHead (expressionValue (extend ρ (5*nb) (5*na)) (va 1))))
        ((5*na+4+(5*nb+1):Nat):Ordinal)):Ordinal)=
        (actualCollapse (ordinalNaturalSum
          (ordinalNaturalProduct Ordinal.omega0 (paddedHead (expressionValue (extend ρ (5*nb) (5*na)) (vb 1))))
          ((5*nb+4+(5*na+1):Nat):Ordinal)):Ordinal)
      rw [hv,hw,he]
      rw [show 5*na+4+(5*nb+1)=5*nb+4+(5*na+1) by omega]
    · change denote _ _=denote _ _
      rw [pad_head,pad_head]
      change paddedHead (expressionValue (extend ρ (5*nb) (5*na)) (va 1))=
        paddedHead (expressionValue (extend ρ (5*nb) (5*na)) (vb 1))
      rw [hv,hw,he]
  · rintro ⟨z,w,h⟩
    have hh := (vectorEqual_iff _ _ _ _ _ hal hbr).mp h 1
    change denote _ _=denote _ _ at hh
    rw [pad_head,pad_head] at hh
    change paddedHead (expressionValue (extend ρ z w) (va 1))=
      paddedHead (expressionValue (extend ρ z w) (vb 1)) at hh
    rw [hv,hw] at hh
    exact paddedHead_injective hh
end LogicLineages.OrdinalComparison.Source.FunctionalDetector.Proof
