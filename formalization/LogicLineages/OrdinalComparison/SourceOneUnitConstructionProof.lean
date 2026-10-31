module
public import LogicLineages.OrdinalComparison.SourceOneUnitSizeProof
public import LogicLineages.OrdinalComparison.SourceOneUnitPartialProof
public import LogicLineages.OrdinalComparison.SourceOneUnitGraphProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem actualHeadConstruction : Targets.ActualHeadConstruction := by
  intro Γ σ τ a
  obtain ⟨h,hA,hAg,hG⟩ := source_bundle a
  obtain ⟨h',hV,hVg,hVG⟩ := source_bundle (unused a)
  have hu := AbsoluteObserver.Proof.unused_assignment a h hA
  have hhu := Option.some.inj (hV.symm.trans hu)
  subst h'
  obtain ⟨l,hL,hLg,hLG⟩ := source_bundle (first a)
  obtain ⟨l',hL',hL'g,hL'G⟩ := source_bundle (second a)
  obtain ⟨ps,hps,hpg⟩ := head_partial h hAg hG
  obtain ⟨ps',hps',hpg'⟩ := head_partial (AbsoluteObserver.Proof.unusedVector h) hVg hVG
  let d : Data := ⟨multiplier h,multiplier (AbsoluteObserver.Proof.unusedVector h),ordinalHeadFree (h 0)⟩
  have hc : compile a=some d := by
    simp only [compile,hA,hV,Option.bind_some]
    rfl
  have hd : 0<d.d := multiplier_positive h
  have hscalar := unused_scalar_literal h
  have hgrowth : d.free=false →
      ordinalPartialSize (AbsoluteObserver.Proof.unusedVector h 0)=
        coefficient τ*ordinalPartialSize (h 0)+3*copies τ ∧
      (∀ j : Fin (τ.level+1), 0<j.val → ordinalPartialSize (h j) ≤
        ordinalPartialSize (AbsoluteObserver.Proof.unusedVector h ⟨j.val,by have := j.isLt; omega⟩)) ∧
      d.d<d.d' := by
    intro hf
    have ha : ordinalHeadFree (h 0)=false := hf
    refine ⟨?_,?_,unused_multiplier_strict h ha⟩
    · rw [unused_scalar_literal]
      exact inflated_size τ (h 0) ha
    · intro j hj
      exact unused_positive_size h j hj
  refine ⟨h,AbsoluteObserver.Proof.unusedVector h,ps,ps',l,l',d,
    hA,hV,hL,hL',hps,hps',hc,rfl,rfl,rfl,hd,hscalar,hgrowth,?_⟩
  intro ρ
  obtain ⟨P,hPpos,hPv⟩ := scalar_nat (ps 0) (hpg 0) ρ
  obtain ⟨R,hRpos,hRv⟩ := scalar_nat (h 0) (hAg 0) (unitExtension (σ := σ) ρ)
  obtain ⟨P',hP'pos,hP'v⟩ := scalar_nat (ps' 0) (hpg' 0) ρ
  obtain ⟨R',hR'pos,hR'v⟩ := scalar_nat (AbsoluteObserver.Proof.unusedVector h 0) (hVg 0) (unitExtension (σ := σ) ρ)
  obtain ⟨L,hLpos,hLv⟩ := scalar_nat (l 0) (hLg 0) ρ
  obtain ⟨L',hL'pos,hL'v⟩ := scalar_nat (l' 0) (hL'g 0) ρ
  have hLe := abstraction_scalar h ps l hps (lambda_value a h l hA hL) ρ P R hPv hRv
  have hLval : L=d.d*P+R := Nat.cast_injective (hLv.symm.trans hLe)
  have hLpe := abstraction_scalar (AbsoluteObserver.Proof.unusedVector h) ps' l' hps'
    (lambda_value (unused a) _ l' hV hL') ρ P' R' hP'v hR'v
  have hLpval : L'=d.d'*P'+R' := Nat.cast_injective (hL'v.symm.trans hLpe)
  have hfree : d.free=true → P=R+1 ∧ L=(d.d+1)*R+d.d := by
    intro hf
    have he := free_partial_value ρ (h 0) hf ps hps R hRv
    have hpeq : P=R+1 := Nat.cast_injective (hPv.symm.trans he)
    refine ⟨hpeq,?_⟩
    rw [hLval,hpeq]
    ring
  have hactive : d.free=false → P'=coefficient τ*P+4*copies τ ∧
      R'=coefficient τ*R+copies τ ∧
      L'=coefficient τ*d.d'*P+coefficient τ*R+constant τ d := by
    intro hf
    have hpi : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (inflated τ (h 0))=some ps' := by
      rw [← unused_scalar_literal h]
      exact hps'
    have hpart := active_partial_value (valuation ρ) τ (h 0) hf ps ps' hps hpi P hPv
    have hpv' : P'=coefficient τ*P+4*copies τ := Nat.cast_injective (hP'v.symm.trans hpart)
    have hret := AbsoluteObserver.Proof.unused_scalar (valuation (unitExtension (σ := σ) ρ)) h R hRv
    have hret' : expressionValue (unitExtension (σ := σ) ρ) (AbsoluteObserver.Proof.unusedVector h 0)=
        ((coefficient τ*R+copies τ : Nat) : Ordinal) := by
      unfold expressionValue
      simpa only [AbsoluteObserver.factor,coefficient,copies,Nat.add_sub_cancel] using hret
    have hrv' : R'=coefficient τ*R+copies τ := Nat.cast_injective (hR'v.symm.trans hret')
    refine ⟨hpv',hrv',?_⟩
    rw [hLpval,hpv',hrv']
    unfold constant
    ring
  refine ⟨P,R,P',R',L,L',hPpos,hRpos,hLpos,hL'pos,hPv,hRv,hP'v,hR'v,hLv,hL'v,hLval,hfree,hactive,?_⟩
  intro r
  exact formula_exact a d ρ l l' hL hL' P R L L' hLpos hL'pos hLv hL'v hLval
    (fun hf => (hfree hf).2) (fun hf => ⟨(hgrowth hf).2.2,(hactive hf).2.2⟩) r
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
