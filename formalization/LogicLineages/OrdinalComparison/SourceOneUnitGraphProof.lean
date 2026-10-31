module
public import LogicLineages.OrdinalComparison.SourceOneUnitScalarProof
public import Mathlib.Tactic.Ring
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment OriginalDomain

theorem observation_iff {Γ τ} (ρ : AdmissibleSubstitution Γ) (a : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (hv : assignment OrdinalSyntax.defaultPolicy a=some v)
    (L : Nat) (hL : expressionValue ρ (v 0)=(L : Ordinal)) (n : Nat) :
    Observation ρ a n ↔ n+1=L := by
  constructor
  · rintro ⟨w,hw,he⟩
    have h := Option.some.inj (hw.symm.trans hv)
    subst w
    exact Nat.cast_injective (he.symm.trans hL)
  · intro h
    exact ⟨v,hv,by rw [h]; exact hL⟩

theorem formula_exact {Γ σ τ} (a : OriginalTerm (σ::Γ) τ) (d : Data)
    (ρ : AdmissibleSubstitution Γ)
    (l : OrdinalVector Γ (Ty.arrow σ τ).level)
    (l' : OrdinalVector Γ (Ty.arrow σ (.arrow .ground τ)).level)
    (hl : assignment OrdinalSyntax.defaultPolicy (first a)=some l)
    (hl' : assignment OrdinalSyntax.defaultPolicy (second a)=some l')
    (P R L L' : Nat) (hLpos : 0<L) (hL'pos : 0<L')
    (hLv : expressionValue ρ (l 0)=(L : Ordinal))
    (hL'v : expressionValue ρ (l' 0)=(L' : Ordinal))
    (hL : L=d.d*P+R)
    (hfree : d.free=true → L=(d.d+1)*R+d.d)
    (hactive : d.free=false → d.d<d.d' ∧
      L'=coefficient τ*d.d'*P+coefficient τ*R+constant τ d)
    (r : Nat) : Formula ρ a d r ↔ r=R := by
  have hp : 0 < coefficient τ := by unfold coefficient; omega
  have hobs := observation_iff ρ (first a) l hl L hLv
  have hobs' := observation_iff ρ (second a) l' hl' L' hL'v
  cases hf : d.free with
  | true =>
    simp only [Formula,hf,↓reduceIte]
    constructor
    · rintro ⟨z,hz,he⟩
      have hzv := (hobs z).mp hz
      have hr := hfree hf
      have hm : (d.d+1)*r=(d.d+1)*R := by omega
      exact Nat.eq_of_mul_eq_mul_left (by omega) hm
    · rintro rfl
      refine ⟨L-1,(hobs _).mpr (by omega),?_⟩
      have hr := hfree hf
      omega
  | false =>
    simp only [Formula,hf,Bool.false_eq_true,↓reduceIte]
    obtain ⟨hg,hlp⟩ := hactive hf
    have hc : 0 < coefficient τ*(d.d'-d.d) := Nat.mul_pos hp (Nat.sub_pos_of_lt hg)
    have hid : coefficient τ*d.d'*L+d.d*constant τ d =
        d.d*L'+coefficient τ*(d.d'-d.d)*R := by
      rw [hL,hlp]
      have hd : d.d+(d.d'-d.d)=d.d' := by omega
      rw [← hd]
      simp only [Nat.add_sub_cancel_left]
      ring
    constructor
    · rintro ⟨z,z',hz,hz',he⟩
      have hzv := (hobs z).mp hz
      have hzv' := (hobs' z').mp hz'
      rw [hzv,hzv'] at he
      have hm : coefficient τ*(d.d'-d.d)*r=coefficient τ*(d.d'-d.d)*R := by omega
      exact Nat.eq_of_mul_eq_mul_left hc hm
    · rintro rfl
      refine ⟨L-1,L'-1,(hobs _).mpr (by omega),(hobs' _).mpr (by omega),?_⟩
      rw [Nat.sub_add_cancel (by omega : 1≤L),Nat.sub_add_cancel (by omega : 1≤L')]
      exact hid
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
