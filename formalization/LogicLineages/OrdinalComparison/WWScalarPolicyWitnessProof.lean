module
public import LogicLineages.OrdinalComparison.WWScalarPolicyWitnessTargets
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem finiteAddValue_sound {ι : Type}
    (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι)
    (n : Nat) (h : finiteAddValue t = some n) (ρ : ι → Ordinal) :
    denote ρ t = (n : Ordinal) := by
  induction t generalizing n with
  | var c => simp [finiteAddValue] at h
  | zero => simp [finiteAddValue] at h
  | one =>
    have hn : 1 = n := by simpa [finiteAddValue] using h
    subst n
    simp [denote]
  | omega => simp [finiteAddValue] at h
  | emul f g hf hg => simp [finiteAddValue] at h
  | collapse f g hf hg => simp [finiteAddValue] at h
  | add f g hf hg =>
    cases hfa : finiteAddValue f with
    | none => simp [finiteAddValue, hfa] at h
    | some a =>
      cases hgb : finiteAddValue g with
      | none => simp [finiteAddValue, hfa, hgb] at h
      | some b =>
        have hn : a + b = n := by simpa [finiteAddValue, hfa, hgb] using h
        subst n
        simp only [denote, hf a hfa, hg b hgb]
        exact naturalSum_finite a b

private theorem head_component_old {Γ : List Ty} {σ τ : Ty}
    (v : Variable Γ τ) (i : Fin (τ.level + 1)) :
    ordinalHeadComponentOccurs (σ := σ) ⟨τ, .there v, i⟩ = false := rfl

private theorem head_component_new {Γ : List Ty} {σ : Ty}
    (i : Fin (σ.level + 1)) :
    ordinalHeadComponentOccurs (Γ := Γ) ⟨σ, .here, i⟩ = true := rfl

private theorem closure_component_old {Γ : List Ty} {σ τ : Ty}
    (v : Variable Γ τ) (i : Fin (τ.level + 1)) :
    ordinalHeadClosureComponent (σ := σ) ⟨τ, .there v, i⟩ = .var ⟨τ, v, i⟩ := rfl

private theorem closure_component_new {Γ : List Ty} {σ : Ty}
    (i : Fin (σ.level + 1)) :
    ordinalHeadClosureComponent (Γ := Γ) ⟨σ, .here, i⟩ = .one := rfl

private theorem polynomial_add_value (a b : WitnessPolynomial) :
    (a.add b).value = a.value + b.value := by
  simp only [WitnessPolynomial.add, WitnessPolynomial.value, Nat.add_mul]
  omega

private theorem atom_value (n : Nat) (a : WitnessPolynomial) (h : witnessAtom n = some a) :
    a.value = witnessH n := by
  unfold witnessAtom at h
  split at h <;> simp_all [WitnessPolynomial.value]
  all_goals rw [← h]; simp [WitnessPolynomial.value]

private theorem omega_product_one : ordinalNaturalProduct Ordinal.omega0 1 = Ordinal.omega0 := by
  let w : NONote := ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩
  let o : NONote := ⟨1, ONote.nf_one⟩
  have hw : w.1.repr = Ordinal.omega0 := by simp [w, ONote.repr]
  have ho : o.1.repr = (1 : Ordinal) := by simp [o, ONote.repr_one]
  calc
    ordinalNaturalProduct Ordinal.omega0 1 = (naturalProduct w o).1.repr := by
      rw [naturalProductDenotation, hw, ho]
    _ = Ordinal.omega0 := by
      have he : (naturalProduct w o).1 = w.1 := by decide +kernel
      rw [he, hw]

theorem actualScalarWitnessPolynomialSound : Targets.ActualScalarWitnessPolynomialSound := by
  intro Γ t a hs
  induction t generalizing a with
  | var c => simp [witnessPolynomial] at hs
  | zero => simp [witnessPolynomial] at hs
  | omega => simp [witnessPolynomial] at hs
  | emul f g ihf ihg => simp [witnessPolynomial] at hs
  | one =>
    have he : (⟨1,0,0,0,0,0⟩ : WitnessPolynomial) = a := Option.some.inj hs
    subst a
    intro ρ
    simp [denote, WitnessPolynomial.value]
  | add f g ihf ihg =>
    obtain ⟨x, hx, y, hy, he⟩ : ∃ x, witnessPolynomial f = some x ∧
        ∃ y, witnessPolynomial g = some y ∧ x.add y = a := by
      simpa only [witnessPolynomial, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hs
    subst a
    intro ρ
    rw [denote, ihf x hx ρ, ihg y hy ρ, polynomial_add_value]
    exact naturalSum_finite _ _
  | collapse f g ihf ihg =>
    obtain ⟨r, hr, n, hn, he⟩ : ∃ r, finiteAddValue f = some r ∧
        ∃ n, finiteAddValue g = some n ∧ (if r = 1 then witnessAtom n else none) = some a := by
      simpa only [witnessPolynomial, bind, pure, Option.bind_eq_some_iff] using hs
    have hr1 : r = 1 := by
      by_contra h
      simp [h] at he
    subst r
    have hatom : witnessAtom n = some a := by simpa using he
    intro ρ
    rw [denote, finiteAddValue_sound f 1 hr ρ, finiteAddValue_sound g n hn ρ]
    simp only [Nat.cast_one]
    rw [omega_product_one, actualNaturalSumFiniteRight, atom_value n a hatom]
    rfl

private theorem left_scalar_computes :
    (witnessScalar .left).bind witnessPolynomial = some witnessLeftPolynomial := by
  simp [witnessScalar, witness, assignment, abstraction, ordinalCanonicalApplication,
    ordinalCanonicalBox, ordinalBoxPositive, ordinalBoxScalarTail, ordinalVectorAt, Ty.level,
    policyPartial, sum3, ordinalHeadFree, ordinalHeadOccurs, head_component_old, head_component_new,
    ordinalFreePartialVector, ordinalHeadClosure, closure_component_old, closure_component_new, substitute,
    ordinalPartialSize, literalRepeat, finiteAddValue, List.finRange_succ, List.finRange_zero,
    witnessPolynomial, witnessAtom, WitnessPolynomial.add, witnessLeftPolynomial]
  decide +kernel

private theorem right_scalar_computes :
    (witnessScalar .right).bind witnessPolynomial = some witnessRightPolynomial := by
  simp [witnessScalar, witness, assignment, abstraction, ordinalCanonicalApplication,
    ordinalCanonicalBox, ordinalBoxPositive, ordinalBoxScalarTail, ordinalVectorAt, Ty.level,
    policyPartial, sum3, ordinalHeadFree, ordinalHeadOccurs, head_component_old, head_component_new,
    ordinalFreePartialVector, ordinalHeadClosure, closure_component_old, closure_component_new, substitute,
    ordinalPartialSize, literalRepeat, finiteAddValue, List.finRange_succ, List.finRange_zero,
    witnessPolynomial, witnessAtom, WitnessPolynomial.add, witnessRightPolynomial]
  decide +kernel

theorem actualClosedScalarPolicySeparation : Targets.ActualClosedScalarPolicySeparation := by
  have hl := left_scalar_computes
  have hr := right_scalar_computes
  cases ha : witnessScalar .left with
  | none => simp [ha] at hl
  | some a =>
    cases hb : witnessScalar .right with
    | none => simp [hb] at hr
    | some b =>
      have hla : witnessPolynomial a = some witnessLeftPolynomial := by simpa [ha] using hl
      have hrb : witnessPolynomial b = some witnessRightPolynomial := by simpa [hb] using hr
      have hleft (ρ : OrdinalComponent [] → Ordinal) : denote ρ a =
          ((388 * (10 * witnessH 20 + witnessH 14 + 10) + 10 * witnessH 8 + witnessH 6 : Nat) : Ordinal) := by
        rw [actualScalarWitnessPolynomialSound [] a witnessLeftPolynomial hla ρ]
        apply congrArg (fun n : Nat => (n : Ordinal))
        simp only [witnessLeftPolynomial, WitnessPolynomial.value]
        omega
      have hright (ρ : OrdinalComponent [] → Ordinal) : denote ρ b =
          ((348 * (10 * witnessH 18 + witnessH 14 + 10) + 10 * witnessH 8 + witnessH 6 : Nat) : Ordinal) := by
        rw [actualScalarWitnessPolynomialSound [] b witnessRightPolynomial hrb ρ]
        apply congrArg (fun n : Nat => (n : Ordinal))
        simp only [witnessRightPolynomial, WitnessPolynomial.value]
        omega
      refine ⟨a, b, ha, hb, hleft, hright, ?_⟩
      intro ρ
      rw [hleft, hright]
      have hm : witnessH 18 ≤ witnessH 20 := actualCollapseFiniteTailMonotone Ordinal.omega0
        (OriginalDomain.originalClosedValueBelowEpsilonZero .omega) 18 20 (by decide)
      have hn : 348 * (10 * witnessH 18 + witnessH 14 + 10) + 10 * witnessH 8 + witnessH 6 <
          388 * (10 * witnessH 20 + witnessH 14 + 10) + 10 * witnessH 8 + witnessH 6 := by omega
      exact_mod_cast hn

end LogicLineages.OrdinalComparison.Source.LiteralPolicy
