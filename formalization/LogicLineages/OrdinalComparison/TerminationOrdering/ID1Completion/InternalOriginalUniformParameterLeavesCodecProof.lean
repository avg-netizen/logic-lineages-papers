module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaDomainCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
open Source InternalOriginalUniformParameterLeaves

theorem actualOriginalUniformParameterCodec :
    InternalOriginalUniformParameterLeavesTargets.ActualOriginalUniformParameterCodec := by
  constructor
  · intro n symbols S Gamma table value
    constructor
    · simp only [parameterCode, Nat.unpair_pair, OrdinaryArithmeticQuotient.contextCode,
        Encodable.encodek]
    · simp only [parameterObject, parameterCode, Nat.unpair_pair]
      exact Encodable.encodek (Gamma,value)
  · intro value parameter
    obtain ⟨obj, hd⟩ := JointGammaDomainCodecProof.actualObjectCodec.1
      (Nat.pair (Nat.unpair parameter).2 value)
    have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1 _ obj).mp hd
    have hv : obj.2 = value := by
      have h := congrArg (fun k : Nat => (Nat.unpair k).2) he
      simpa only [ContextUniform.objectCode, Encodable.encode_prod_val,
        Encodable.encode_nat, Nat.unpair_pair] using h
    refine ⟨obj.1, ?_⟩
    unfold parameterObject
    rw [hd]
    cases obj with
    | mk Gamma x => simp_all

theorem decodedValueAtParameter (n : Nat)
    (f : OrdinaryArithmeticQuotient.Context n → ContextUniform.Object → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (value : Nat) :
    decodedValue n f value (parameterCode symbols S Gamma table) =
      f ((symbols,S),table) (Gamma,value) := by
  obtain ⟨hc,ho⟩ := actualOriginalUniformParameterCodec.1 n symbols S Gamma table value
  simp only [decodedValue, hc, ho]

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
