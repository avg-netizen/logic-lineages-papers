module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRootProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericCarrier
open InternalOriginalUniformParameterLeaves
open OriginalHereditaryValidity OriginalHereditaryValidityRecurrence

/-- Every constructor's own result type is explicitly checked by the original
universe predicate, without any closure assumption on the window. -/
theorem resultInWindow {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} {tau : Ty}
    (symbols : List (Fin n)) (S : List Ty) (q : AuxTerm (Fin n) arity Gamma tau)
    (hq : InUniverse symbols S q) : tau ∈ S := by
  cases q <;> first | exact hq.1 | exact hq.1.1

theorem sourceBoolean (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) :
    sourceValue n arity v = 0 ∨ sourceValue n arity v = 1 := by
  unfold sourceValue decodedValue
  cases Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 1)).1 with
  | none => exact Or.inl rfl
  | some ctx =>
    cases parameterObject (v.get 0) (v.get 1) with
    | none => exact Or.inl rfl
    | some obj =>
      cases rawCarrierTest n arity ctx.1.1 ctx.1.2 obj.1 obj.2 <;> simp

/-- Recover the literal original context number and the actual encoded Gamma.
No canonical encoding of the decoded outer context is imposed. -/
theorem sourceTyped (n : Nat) (arity : Fin n → Nat) (value parameter : Nat)
    (h : sourceValue n arity (List.Vector.ofFn ![value,parameter]) = 1) :
    TypedWindowFrame n arity (Nat.unpair parameter).1 ⟨value,parameter⟩ := by
  obtain ⟨Gamma,ho⟩ :=
    InternalOriginalUniformParameterLeavesCodecProof.actualOriginalUniformParameterCodec.2 value parameter
  have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1 _ (Gamma,value)).mp ho
  have hg : Encodable.encode Gamma = (Nat.unpair parameter).2 := by
    have hh := congrArg (fun k : Nat => (Nat.unpair k).1) he
    simpa only [ContextUniform.objectCode,Encodable.encode_prod_val,Encodable.encode_nat,
      Nat.unpair_pair] using hh
  cases hd : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair parameter).1 with
  | none =>
    simp only [sourceValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
      Matrix.cons_val_one,hd] at h
    contradiction
  | some ctx =>
    have ht : rawCarrierTest n arity ctx.1.1 ctx.1.2 Gamma value = true := by
      simpa only [sourceValue,decodedValue,List.Vector.get_ofFn,Matrix.cons_val_zero,
        Matrix.cons_val_one,hd,ho,Bool.toNat_eq_one] using h
    obtain ⟨⟨tau,q⟩,hq,hn⟩ :=
      (NumberedNumericCarrierProof.rawCarrierTestCorrect n arity ctx.1.1 ctx.1.2 Gamma value).mp ht
    refine ⟨ctx,hd,Gamma,?_,tau,q,hn.symm,resultInWindow _ _ q hq,hq⟩
    change parameter = Nat.pair (Nat.unpair parameter).1 (Encodable.encode Gamma)
    rw [hg,Nat.pair_unpair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityRecurrenceSourceRootProof
