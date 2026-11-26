module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
open Source InternalOriginalUniformParameterLeaves InternalOriginalStepGuard

/-- Every raw Gamma number has its actual original list decoding. The raw
outer Context number is not replaced by a preferred re-encoding. -/
theorem parameterGamma (parameter : Nat) :
    ∃ Gamma : List Ty, Encodable.encode Gamma = (Nat.unpair parameter).2 := by
  obtain ⟨Gamma,ho⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2 0 parameter
  have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1 _ (Gamma,0)).mp ho
  refine ⟨Gamma,?_⟩
  have hh := congrArg (fun k : Nat => (Nat.unpair k).1) he
  simpa only [ContextUniform.objectCode,Encodable.encode_prod_val,Encodable.encode_nat,
    Nat.unpair_pair] using hh

theorem objectAtGamma (value parameter : Nat) (Gamma : List Ty)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2) :
    parameterObject value parameter = some (Gamma,value) := by
  unfold parameterObject
  rw [← hg]
  exact Encodable.encodek (Gamma,value)

theorem sourceAtParameter (n : Nat) (arity : Fin n → Nat) (value parameter : Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hc : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2) :
    sourceValue n arity (List.Vector.ofFn ![value,parameter]) =
      sourceValidityValue n arity ctx.1.1 ctx.1.2 Gamma value := by
  simp only [sourceValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Matrix.cons_val_one,hc,objectAtGamma value parameter Gamma hg]
  rfl

theorem targetAtParameter (n : Nat) (arity : Fin n → Nat) (value parameter : Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hc : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2) :
    targetValue n arity (List.Vector.ofFn ![value,parameter]) =
      targetValidityValue n arity Gamma value := by
  simp only [targetValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Matrix.cons_val_one,hc,objectAtGamma value parameter Gamma hg]
  exact InternalOriginalUniformParameterLeavesCalibrationProof.targetCalibration n arity Gamma value

theorem memberAtParameter (n : Nat) (value parameter : Nat)
    (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
    (hc : Encodable.decode (Nat.unpair parameter).1 = some ctx)
    (hg : Encodable.encode Gamma = (Nat.unpair parameter).2) :
    memberValue n (List.Vector.ofFn ![value,parameter]) =
      InternalStructuralEndpointGuard.membershipValue ctx.1.2 value := by
  simp only [memberValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
    Matrix.cons_val_one,hc,objectAtGamma value parameter Gamma hg]

theorem targetBoolean (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) :
    targetValue n arity v = 0 ∨ targetValue n arity v = 1 := by
  unfold targetValue decodedValue
  cases Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none => exact Or.inl rfl
  | some ctx =>
    cases parameterObject (v.get 0) (v.get 1) with
    | none => exact Or.inl rfl
    | some obj =>
      cases hd : NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2 <;> simp [hd]

theorem sourceImpliesTarget (n : Nat) (arity : Fin n → Nat) (value parameter : Nat)
    (hs : sourceValue n arity (List.Vector.ofFn ![value,parameter]) = 1) :
    targetValue n arity (List.Vector.ofFn ![value,parameter]) = 1 := by
  obtain ⟨Gamma,hg⟩ := parameterGamma parameter
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1 with
  | none =>
    simp [sourceValue,decodedValue,hc] at hs
  | some ctx =>
    rw [sourceAtParameter n arity value parameter ctx Gamma hc hg] at hs
    rw [targetAtParameter n arity value parameter ctx Gamma hc hg]
    unfold sourceValidityValue NumberedNumericCarrier.rawCarrierTest
      NumberedNumericCarrier.decodeUniverse at hs
    unfold targetValidityValue
    cases hd : NumberedNumericDecoding.decodePackedNumber n arity Gamma value with
    | none => simp [hd] at hs
    | some q => simp [hd]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityParameterProof
