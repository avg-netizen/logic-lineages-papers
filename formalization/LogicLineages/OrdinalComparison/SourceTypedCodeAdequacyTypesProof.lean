module
public import LogicLineages.OrdinalComparison.SourceTypedCodeAdequacyTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Proof
open SyntaxCode

theorem type_code_injective : Function.Injective typeCode := by
  intro τ υ h
  have hd := congrArg decodeType h
  exact (SyntaxCode.Proof.typeDecodeEncode τ).symm.trans (hd.trans (SyntaxCode.Proof.typeDecodeEncode υ))

theorem fixedContextTypeUniqueness : Targets.FixedContextTypeUniqueness := by
  intro Γ τ υ t u h
  have ht := (SyntaxCode.Proof.typedRawExact Γ τ (erase t)).2 ⟨t,rfl⟩
  have hu := (SyntaxCode.Proof.typedRawExact Γ υ (erase u)).2 ⟨u,rfl⟩
  rw [h] at ht
  exact type_code_injective (Option.some.inj (ht.symm.trans hu))

theorem variable_index_injective {Γ τ} (x y : Variable Γ τ)
    (h : SourceTypedPorts.variableIndex x=SourceTypedPorts.variableIndex y) : x=y := by
  induction x with
  | here => cases y with
    | here => rfl
    | there y => simp [SourceTypedPorts.variableIndex] at h
  | there x ih => cases y with
    | here => simp [SourceTypedPorts.variableIndex] at h
    | there y =>
      apply congrArg Variable.there
      apply ih
      simpa only [SourceTypedPorts.variableIndex,Nat.add_right_cancel_iff] using h
end LogicLineages.OrdinalComparison.Source.SourceTypedCodeAdequacy.Proof
