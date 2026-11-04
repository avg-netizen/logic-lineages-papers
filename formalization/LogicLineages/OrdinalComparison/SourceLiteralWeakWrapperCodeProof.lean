module
public import LogicLineages.OrdinalComparison.SourceLiteralWeakWrapperCodeTargets
public import LogicLineages.OrdinalComparison.SourceMachineInternalLevelProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceLiteralWeakWrapperCode.Proof
open ParametricLiteralWeakWrapper

/-- The operand stays outside the binder, with its original code unchanged. -/
theorem exactEncoding : Targets.ExactEncoding := by
  intro Γ t
  exact ⟨rfl,rfl⟩

/-- Both literal application-code constructors are primitive recursive. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  constructor
  · exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 8)
        (Primrec₂.natPair.comp (Primrec.const 6) Primrec.id)) (Primrec.const 5)
  · exact Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 8)
        (Primrec₂.natPair.comp (Primrec.const (8*Nat.pair 0 1+6)) Primrec.id)) (Primrec.const 5)

/-- The literal identity and constant functions add only a ground binder. -/
theorem fragmentPreservation : Targets.FragmentPreservation := by
  intro Γ t ht
  exact ⟨⟨⟨rfl,True.intro⟩,ht⟩,⟨⟨rfl,True.intro⟩,ht⟩⟩

/-- With ground free variables, the structural internal-level bound is preserved. -/
theorem internalLevelPreservation : Targets.InternalLevelPreservation := by
  intro Γ t hΓ ht
  have hf := fragmentPreservation Γ t ht
  exact ⟨SourceMachineInternalLevel.Proof.structuralLevel Γ .ground (identityApply t) hΓ hf.1,
    SourceMachineInternalLevel.Proof.structuralLevel Γ .ground (constantApply t) hΓ hf.2⟩
end LogicLineages.OrdinalComparison.Source.SourceLiteralWeakWrapperCode.Proof
