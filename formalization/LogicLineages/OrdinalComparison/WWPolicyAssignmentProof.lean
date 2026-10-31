module
public import LogicLineages.OrdinalComparison.WWPolicyAssignmentTargets
public import LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPolicy
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem actualLeftPolicyPartialCalibration : Targets.ActualLeftPolicyPartialCalibration := by
  intro Γ σ i t
  induction t generalizing i with
  | var c => rfl
  | zero => rfl
  | one => rfl
  | omega => rfl
  | add f g hf hg =>
    rw [policyPartial, ordinalTypedPartial]
    split
    · rfl
    · simp only [hf, hg, sum3]
  | emul f g hf hg =>
    rw [policyPartial, ordinalTypedPartial]
    split
    · rfl
    · simp only [hf, hg]
  | collapse f g hf hg =>
    rw [policyPartial, ordinalTypedPartial]
    split
    · rfl
    · simp only [hf, hg]

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

private theorem left_witness_computes :
    (witnessPositive .left).bind finiteAddValue = some 204 := by
  simp [witnessPositive, witness, assignment, abstraction, ordinalCanonicalApplication,
    ordinalCanonicalBox, ordinalBoxPositive, ordinalBoxScalarTail, ordinalVectorAt, Ty.level,
    policyPartial, sum3, ordinalHeadFree, ordinalHeadOccurs, head_component_old, head_component_new,
    ordinalFreePartialVector, ordinalHeadClosure, closure_component_old, closure_component_new, substitute,
    ordinalPartialSize, literalRepeat, finiteAddValue, List.finRange_succ, List.finRange_zero]
  decide +kernel

private theorem right_witness_computes :
    (witnessPositive .right).bind finiteAddValue = some 184 := by
  simp [witnessPositive, witness, assignment, abstraction, ordinalCanonicalApplication,
    ordinalCanonicalBox, ordinalBoxPositive, ordinalBoxScalarTail, ordinalVectorAt, Ty.level,
    policyPartial, sum3, ordinalHeadFree, ordinalHeadOccurs, head_component_old, head_component_new,
    ordinalFreePartialVector, ordinalHeadClosure, closure_component_old, closure_component_new, substitute,
    ordinalPartialSize, literalRepeat, finiteAddValue, List.finRange_succ, List.finRange_zero]
  decide +kernel

theorem actualClosedSourcePolicySeparation : Targets.ActualClosedSourcePolicySeparation := by
  have hl := left_witness_computes
  have hr := right_witness_computes
  cases ha : witnessPositive .left with
  | none => simp [ha] at hl
  | some a =>
    cases hb : witnessPositive .right with
    | none => simp [hb] at hr
    | some b =>
      have hla : finiteAddValue a = some 204 := by simpa [ha] using hl
      have hrb : finiteAddValue b = some 184 := by simpa [hb] using hr
      refine ⟨a, b, ha, hb, finiteAddValue_sound a 204 hla,
        finiteAddValue_sound b 184 hrb, ?_⟩
      intro ρ
      rw [finiteAddValue_sound a 204 hla ρ, finiteAddValue_sound b 184 hrb ρ]
      norm_num

end LogicLineages.OrdinalComparison.Source.LiteralPolicy
