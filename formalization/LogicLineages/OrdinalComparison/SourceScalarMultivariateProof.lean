module
public import LogicLineages.OrdinalComparison.SourceScalarMultivariateTargets
public import LogicLineages.OrdinalComparison.WWFixedShiftProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateSourceBridge
open Source.ForwardTranslation
open Vendor.R1

private theorem sum_without : ∀ a b : ONote,
    RawWithoutFinitePart a → RawWithoutFinitePart b → RawWithoutFinitePart (rawNaturalSum a b)
  | .zero, b, _, hb => by simpa only [rawNaturalSum] using hb
  | a, .zero, ha, _ => by cases a <;> simpa only [rawNaturalSum] using ha
  | .oadd e c t, .oadd f d u, ha, hb => by
    cases h : ONote.cmp e f with
    | lt =>
      simp only [rawNaturalSum,h,RawWithoutFinitePart]
      exact ⟨hb.1,sum_without (.oadd e c t) u ha hb.2⟩
    | eq =>
      simp only [rawNaturalSum,h,RawWithoutFinitePart]
      exact ⟨ha.1,sum_without t u ha.2 hb.2⟩
    | gt =>
      simp only [rawNaturalSum,h,RawWithoutFinitePart]
      exact ⟨ha.1,sum_without t (.oadd f d u) ha.2 hb⟩
termination_by a b _ _ => sizeOf a+sizeOf b
decreasing_by all_goals simp_wf; simp only [sizeOf,ONote._sizeOf_1]; omega

private theorem omega_monomial_without (c : PNat) : ∀ b : ONote,
    RawWithoutFinitePart (rawMonomialProduct 1 c b)
  | .zero => True.intro
  | .oadd e d t => by
    have hn : rawNaturalSum 1 e≠0 := by
      intro h
      have hw := rawNaturalSum_norm 1 e
      rw [h] at hw
      change 0=1+treeWeight e at hw
      omega
    exact sum_without _ _ ⟨hn,True.intro⟩ (omega_monomial_without c t)

private theorem omega_product_without (b : ONote) :
    RawWithoutFinitePart (rawNaturalProduct profileOmegaNote.1 b) := by
  change RawWithoutFinitePart
    (rawNaturalSum (rawMonomialProduct 1 1 b) (rawNaturalProduct .zero b))
  exact sum_without _ _ (omega_monomial_without 1 b) True.intro

private theorem without_semantic : ∀ a : ONote,
    RawWithoutFinitePart a → a.repr=0 ∨ Order.IsSuccLimit a.repr
  | .zero, _ => Or.inl rfl
  | .oadd e c t, ha => by
    have he : e.repr≠0 := by
      cases e with
      | zero => exact False.elim (ha.1 rfl)
      | oadd f d u =>
        exact (show (0 : Ordinal)<(ONote.oadd f d u).repr from ONote.oadd_pos f d u).ne'
    have hl : Order.IsSuccLimit (Ordinal.omega0^e.repr*((c : Nat) : Ordinal)) :=
      Ordinal.isSuccLimit_mul_left
        (Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 he)
        (by exact_mod_cast c.pos)
    rcases without_semantic t ha.2 with ht | ht
    · apply Or.inr
      change Order.IsSuccLimit (Ordinal.omega0^e.repr*((c : Nat) : Ordinal)+t.repr)
      rw [ht,add_zero]
      exact hl
    · exact Or.inr (Ordinal.isSuccLimit_add _ ht)

theorem raw_omega_without : Targets.RawOmegaNoFinitePart :=
  ⟨sum_without,omega_product_without,without_semantic⟩

theorem scalar_head_value (c : ClosedPositive) : (scalarHeadNote c).1.repr=fixedHead c := by
  rw [scalarHeadNote,naturalProductDenotation]
  simp [fixedHead,ONote.repr]

theorem head_limit : Targets.SourceScalarFixedLimit := by
  intro c
  have hn : (scalarHeadNote c).1.repr≠0 := by
    rw [scalar_head_value]
    exact (Ordinal.omega0_pos.trans_le (scalarFixedHeadAdmissible c).1).ne'
  have hw : RawWithoutFinitePart (scalarHeadNote c).1 := omega_product_without c.evaluate.1
  rcases without_semantic (scalarHeadNote c).1 hw with hz | hl
  · exact False.elim (hn hz)
  · exact ⟨hl,normalRepresentationSound (scalarHeadNote c),scalar_head_value c⟩

private theorem adapter_code {ι : Type} (index : ι → Nat) (s : Scalar ι) :
    multivariatePositiveEncode (scalarToMultivariate index s)=scalarCode index s := by
  induction s with
  | one => rfl
  | var x => rfl
  | add a b iha ihb => simp only [scalarToMultivariate,multivariatePositiveEncode,scalarCode,iha,ihb]
  | shift c a ih => simp only [scalarToMultivariate,multivariatePositiveEncode,scalarCode,ih]

private theorem adapter_valid {ι : Type} (index : ι → Nat) (d : Nat) (s : Scalar ι)
    (hv : scalarVariablesBelow index d s) : multivariatePositiveValid d (scalarToMultivariate index s) := by
  induction s with
  | one => trivial
  | var x => exact hv
  | add a b iha ihb => exact ⟨iha hv.1,ihb hv.2⟩
  | shift c a ih => exact ⟨(head_limit c).1,(head_limit c).2.1,ih hv⟩

private theorem adapter_value {ι : Type} (index : ι → Nat) (s : Scalar ι) (ρ : Nat → Nat) :
    actualMultivariatePositiveEval (scalarToMultivariate index s) ρ=s.value (fun x => ρ (index x)) := by
  induction s with
  | one => rfl
  | var x => rfl
  | add a b iha ihb => exact congrArg₂ (·+·) iha ihb
  | shift c a ih =>
    simp only [scalarToMultivariate,actualMultivariatePositiveEval,actualProfileHead,
      Scalar.value,scalar_head_value,ih]

theorem adapter : Targets.SourceScalarMultivariateAdapter :=
  ⟨fun _ => adapter_code,fun _ => adapter_valid,fun _ => adapter_value⟩

end LogicLineages.OrdinalComparison.MultivariateSourceBridge
