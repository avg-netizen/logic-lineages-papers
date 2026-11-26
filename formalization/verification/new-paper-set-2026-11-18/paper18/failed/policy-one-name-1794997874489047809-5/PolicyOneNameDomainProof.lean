module
public import LogicLineages.StandardControlCurrent.PolicyOneNameTargets
public import LogicLineages.StandardControlCurrent.DefaultSourceDomainProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyOneName.Proof
open OrdinalComparison Source Source.ForwardTranslation Source.OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem vector_calibration {n : Nat} (v : OrdinalVector [Ty.ground] n)
    (s : AdmissibleSubstitution [Ty.ground]) (x : Nat)
    (hx : ∀ c, valuation s c=(x : Ordinal)) (j : Nat) :
    PolicySourceEquality.vectorAt v s j=sourceVectorAtValue v (fun _ => x) j := by
  have he : valuation s = fun _ => (x : Ordinal) := funext hx
  simp only [PolicySourceEquality.vectorAt,sourceVectorAtValue,ordinalVectorAt]
  split <;> simp only [expressionValue,he,denote]

theorem atom_domain (p : AdmissibleSum.Policy) {τ υ : Ty} (r : OneInputOrderRelation)
    (a : OriginalTerm [Ty.ground] τ) (b : OriginalTerm [Ty.ground] υ)
    (s : AdmissibleSubstitution [Ty.ground]) (x : Nat)
    (hx : ∀ c, valuation s c=(x : Ordinal)) :
    originalAtom p r a b s ↔ actualOneNameSourceAtom p r a b x := by
  unfold originalAtom actualOneNameSourceAtom
  apply exists_congr; intro av
  apply exists_congr; intro bv
  apply and_congr_right; intro ha
  apply and_congr_right; intro hb
  cases r with
  | equal =>
    unfold GroundSourceEquality.SourceEqualityAt
    simp only [vector_calibration _ s x hx]
  | weak =>
    simp only [vector_calibration _ s x hx,SourceComparisonAt,Bool.false_eq_true,if_false]
    constructor
    · intro h; exact ⟨fun j => h (j+1),h 0⟩
    · rintro ⟨hp,hz⟩ j
      cases j with
      | zero => exact hz
      | succ j => exact hp j
  | strict =>
    simp only [vector_calibration _ s x hx,SourceComparisonAt,if_true]
    exact and_comm

theorem original_value : PolicyOneNameTargets.OriginalValue := by
  intro p formula s x hx
  induction formula with
  | truth b => rfl
  | atom r a b =>
    apply Bool.eq_iff_iff.mpr
    simp only [originalValue,actualOneNameSourceBooleanValue,decide_eq_true_eq]
    exact atom_domain p r a b s x hx
  | neg f ih => exact congrArg Bool.not ih
  | conj a b iha ihb => exact congrArg₂ Bool.and iha ihb
  | disj a b iha ihb => exact congrArg₂ Bool.or iha ihb

theorem component_unique (c : OrdinalComponent [Ty.ground]) :
    c=⟨Ty.ground,Variable.here,0⟩ := by
  rcases c with ⟨τ,v,j⟩
  cases v with
  | here =>
    have hj : j=0 := Fin.ext (by have h:=j.isLt; change j.val<1 at h; omega)
    subst j; rfl
  | there v => cases v

theorem original_positive (s : AdmissibleSubstitution [Ty.ground]) :
    ∃ x : Nat, 0<x ∧ ∀ c, valuation s c=(x : Ordinal) := by
  obtain ⟨ρ,hp,hv⟩ := DefaultSourceDomainProof.domain.2 [Ty.ground] (by simp) s
  refine ⟨ρ ⟨Ty.ground,Variable.here,0⟩,hp _,?_⟩
  intro c
  rw [hv c,component_unique c]

theorem positive_original (x : Nat) (hx : 0<x) :
    ∃ s : AdmissibleSubstitution [Ty.ground], ∀ c, valuation s c=(x : Ordinal) :=
  DefaultSourceDomainProof.domain.1 [Ty.ground] (by simp) (fun _ => x) (fun _ => hx)
end LogicLineages.StandardControlCurrent.PolicyOneName.Proof
