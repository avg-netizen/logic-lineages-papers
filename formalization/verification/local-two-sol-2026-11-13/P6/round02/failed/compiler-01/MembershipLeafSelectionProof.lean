module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipLeafSelectionProof
open Source Membership InternalOriginalUniformParameterLeaves
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] Primrec

theorem entriesPrimitive {n : Nat} {A : Type} [Primcodable A]
    (f : A → List (NumberedUniformPackedDecoding.RawPacked n)) (hf : Primrec f) :
    Primrec (fun a => entriesCode (f a)) := by
  have hs : Primrec (fun p : A × NumberedUniformPackedDecoding.RawPacked n × Nat =>
      1 + Nat.pair (Encodable.encode p.2.1) p.2.2) := by
    simpa only [Nat.succ_eq_add_one,Nat.add_comm] using
      Primrec.succ.comp (Primrec₂.natPair.comp
        (Primrec.encode.comp (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
  have hfold := Primrec.list_foldr hf (Primrec.const 0) hs.to₂
  apply hfold.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons head tail ih => simpa only [List.foldr_cons,entriesCode,List.map_cons,
      NumberedMultisetNumeric.numbersNumber] using congrArg (fun r => 1 + Nat.pair (Encodable.encode head) r) ih

theorem listPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (listValue n arity) := by
  apply InternalOriginalUniformParameterLeavesPrimitiveProof.decodedValuePrimitive n
    (fun p => ((NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2).map
      (fun q => entriesCode (ContextUniformPrimary.primaryList arity p.1.1.1 p.1.1.2 p.2.1 q))).getD 0)
  let Input := OrdinaryArithmeticQuotient.Context n × ContextUniform.Object
  have hd : Primrec (fun p : Input =>
      NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have hs : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n =>
      ContextUniformPrimary.primaryList arity p.1.1.1.1 p.1.1.1.2 p.1.2.1 p.2) :=
    (ContextUniformPrimaryPrimitiveProof.primaryListPrimitive n arity).comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have he := entriesPrimitive _ hs
  exact Primrec.option_getD.comp (Primrec.option_map hd he.to₂) (Primrec.const 0)

theorem candidatePrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (candidateValue n arity) := by
  apply InternalOriginalUniformParameterLeavesPrimitiveProof.decodedValuePrimitive n
    (fun p => ((NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2).map Encodable.encode).getD 0)
  let Input := OrdinaryArithmeticQuotient.Context n × ContextUniform.Object
  have hd : Primrec (fun p : Input =>
      NumberedUniformPackedDecoding.rawPackedDecode n arity p.2.1 p.2.2) :=
    (NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity).comp Primrec.snd
  have he : Primrec (fun p : Input × NumberedUniformPackedDecoding.RawPacked n => Encodable.encode p.2) :=
    Primrec.encode.comp Primrec.snd
  exact Primrec.option_getD.comp (Primrec.option_map hd he.to₂) (Primrec.const 0)

theorem actualLeafSelection : MembershipTargets.ActualLeafSelection := by
  intro n arity
  obtain ⟨L,hL⟩ := Proof.allPrimitiveFunctions 2 _ (listPrimitive n arity)
  obtain ⟨D,hD⟩ := Proof.allPrimitiveFunctions 2 _ (candidatePrimitive n arity)
  exact ⟨L,D,hL,hD⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipLeafSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.MembershipLeafSelectionProof
