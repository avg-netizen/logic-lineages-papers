module
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainTargets
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialProof
public import LogicLineages.OrdinalComparison.WWAdmissibleExpansionProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentBoundProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPartialDomain
open AdmissibleSum AdmissiblePartial

private theorem free_success {Γ : List Ty} {σ : Ty} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true) :
    ∃ v, run p i t = some v := by
  refine ⟨ordinalFreePartialVector i t, ?_⟩
  rw [run.eq_def, hf]
  rfl

private theorem domain_success {Γ : List Ty} {σ : Ty} (p : Policy) {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (h : Domain Γ σ i t) :
    ∃ v, run p i t = some v := by
  induction h with
  | free i t hf => exact free_success p i t hf
  | tracked k =>
    refine ⟨fun _ => .one, ?_⟩
    simp [run, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
  | @add i f g df dg ihf ihg =>
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_success p i (.add f g) hf
    · obtain ⟨pf, hpf⟩ := ihf
      obtain ⟨pg, hpg⟩ := ihg
      refine ⟨fun j => three p .activeAdd (pf j) (pg j) .one, ?_⟩
      rw [run, Bool.eq_false_iff.mpr hf, hpf, hpg]
      rfl
  | @emul i f g hi df dg ihf ihg =>
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_success p i (.emul f g) hf
    · obtain ⟨pf, hpf⟩ := ihf
      obtain ⟨pg, hpg⟩ := ihg
      refine ⟨fun j => three p .activeExp (twice p (pf j)) (pg j) .one, ?_⟩
      rw [run, Bool.eq_false_iff.mpr hf, if_pos hi, hpf, hpg]
      rfl
  | @collapse f g df dg ihf ihg =>
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_success p 0 (.collapse f g) hf
    · obtain ⟨pf, hpf⟩ := ihf
      obtain ⟨pg, hpg⟩ := ihg
      refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j), ?_⟩
      rw [run, Bool.eq_false_iff.mpr hf, if_pos rfl, hpf, hpg]
      rfl

private theorem success_domain {Γ : List Ty} {σ : Ty} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ)
    (hv : run p i t = some v) : Domain Γ σ i t := by
  induction t generalizing i v with
  | zero => exact .free i .zero rfl
  | one => exact .free i .one rfl
  | omega => exact .free i .omega rfl
  | var c =>
    rcases c with ⟨τ, x, k⟩
    cases x with
    | here =>
      by_cases hi : i = k.val
      · subst i
        exact .tracked k
      · simp [run, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs, hi] at hv
    | there x => exact .free i _ rfl
  | add f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact .free i _ hf
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      have he : ∃ pf : OrdinalPartialVector Γ σ,
          run p i f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
          run p i g = some pg ∧
          (fun j => three p .activeAdd (pf j) (pg j) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure,
          Option.bind_eq_some_iff, Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, he⟩ := he
      exact .add (ihf i pf hpf) (ihg i pg hpg)
  | emul f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact .free i _ hf
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : 0 < i
      · rw [if_pos hi] at hv
        have he : ∃ pf : OrdinalPartialVector Γ σ,
            run p (i + 1) f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            run p i g = some pg ∧
            (fun j => three p .activeExp (twice p (pf j)) (pg j) .one) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, he⟩ := he
        exact .emul hi (ihf (i + 1) pf hpf) (ihg i pg hpg)
      · simp [hi] at hv
  | collapse f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact .free i _ hf
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = 0
      · rw [if_pos hi] at hv
        have he : ∃ pf : OrdinalPartialVector Γ σ,
            run p 1 f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            run p 0 g = some pg ∧
            (fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
              else .add (pf j) (pg j)) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, he⟩ := he
        subst i
        exact .collapse (ihf 1 pf hpf) (ihg 0 pg hpg)
      · simp [hi] at hv

theorem actualLiteralPartialDomain : Targets.ActualLiteralPartialDomain := by
  intro Γ σ p i t
  exact ⟨domain_success p, fun ⟨v, hv⟩ => success_domain p i t v hv⟩

theorem actualLiteralPartialUniqueBound : Targets.ActualLiteralPartialUniqueBound := by
  intro Γ σ p i t h
  obtain ⟨v, hv⟩ := domain_success p h
  refine ⟨v, ⟨hv, AdmissibleExpansion.actualAdmissiblePartialExpansion Γ σ p i t v hv⟩, ?_⟩
  intro w hw
  exact Option.some.inj (hw.1.symm.trans hv)

theorem actualRepairedFiniteExpansion : Targets.ActualRepairedFiniteExpansion :=
  ⟨actualLiteralPartialDomain, actualLiteralPartialUniqueBound,
    AdmissibleAssignmentBound.actualAdmissibleUniqueBoundedAssignment,
    AdmissiblePartial.actualAdmissiblePartialValue⟩

end LogicLineages.OrdinalComparison.Source.LiteralPartialDomain
