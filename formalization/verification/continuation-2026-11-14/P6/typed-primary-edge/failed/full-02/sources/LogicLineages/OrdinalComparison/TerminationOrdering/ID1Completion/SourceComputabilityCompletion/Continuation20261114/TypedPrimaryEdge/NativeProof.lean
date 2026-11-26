module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SeededPrimaryPool.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.NativeProof
open Source NumberedUniformPackedDecoding
open InternalOriginalUniformParameterLeaves TwoSol20261113.CalibratedPrimary
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] Primrec

theorem structuralPackedPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : ContextUniformPrimary.Window n × RawPacked n × RawPacked n =>
      NumberedExchangeCode.codeExchange arity p.1.1 p.1.2 p.2.1.2 p.2.2.2) :=
  (NumberedExchangeCodePrimrecProof.codeExchangePrimitive n arity).comp
    (Primrec.fst.pair ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
theorem structuralPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (structuralValue n arity) := by
  let V := List.Vector Nat 3
  let Ctx := OrdinaryArithmeticQuotient.Context n
  have getP (i : Fin 3) : Primrec (fun v : V => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp (getP 2)))
  have ha : Primrec (fun v : V => Encodable.decode (α := RawPacked n) (v.get 0)) :=
    Primrec.decode.comp (getP 0)
  have hb : Primrec (fun v : V => Encodable.decode (α := RawPacked n) (v.get 1)) :=
    Primrec.decode.comp (getP 1)
  have he : Primrec (fun p : ((V × Ctx) × RawPacked n) × RawPacked n =>
      (NumberedExchangeCode.codeExchange arity p.1.1.2.1.1 p.1.1.2.1.2 p.1.2.2 p.2.2).toNat) :=
    (Primrec.dom_bool Bool.toNat).comp
      ((structuralPackedPrimitive n arity).comp
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))
  have hm := Primrec.option_map (hb.comp (Primrec.fst.comp Primrec.fst)) he.to₂
  have hi := Primrec.option_bind (ha.comp Primrec.fst) hm.to₂
  have ho := Primrec.option_getD.comp (Primrec.option_bind hc hi.to₂) (Primrec.const 0)
  apply ho.of_eq
  intro v
  cases hc : Encodable.decode (α := Ctx) (Nat.unpair (v.get 2)).1 <;>
    cases ha : Encodable.decode (α := RawPacked n) (v.get 0) <;>
    cases hb : Encodable.decode (α := RawPacked n) (v.get 1) <;>
    simp only [structuralValue,hc,ha,hb,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]


/-- The original product decoder fixes the actual numeric left field even on
codes for which the structural component is not typed-valid. -/
theorem decodedTypeField (n value : Nat) (q : RawPacked n)
    (h : Encodable.decode (α := RawPacked n) value = some q) :
    Encodable.encode q.1 = (Nat.unpair value).1 := by
  rw [Encodable.decode_prod_val] at h
  change (some (NumberedTypeCodecPrimrec.typeEquiv.symm (Nat.unpair value).1)).bind
    (fun t => (Encodable.decode (α := NumberedAuxiliaryCoding.Code (Fin n)) (Nat.unpair value).2).map
      (Prod.mk t)) = some q at h
  cases hd : Encodable.decode (α := NumberedAuxiliaryCoding.Code (Fin n)) (Nat.unpair value).2 with
  | none => simp only [hd,Option.bind_some,Option.map_none] at h; cases h
  | some c =>
    simp only [hd,Option.bind_some,Option.map_some,Option.some.injEq] at h
    rw [← h]
    exact NumberedTypeCodecPrimrec.typeEquiv.apply_symm_apply _

theorem fieldValue (i : Fin 3) (v : List.Vector Nat 3) :
    evaluate (typeField i) v = (Nat.unpair (v.get i)).1 := by
  change evaluate InternalUnpair.left (List.Vector.ofFn ![v.get i]) = _
  rw [InternalEqualityTestEvaluationProof.vectorOne]
  exact (InternalUnpairEvaluationProof.exactUnpairEvaluation (v.get i)).1

theorem guardValue (v : List.Vector Nat 3) : evaluate typeGuard v =
    if (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 then 1 else 0 := by
  change evaluate InternalEqualityTest.equalityTest
    (List.Vector.ofFn ![evaluate (typeField 0) v,evaluate (typeField 1) v]) = _
  rw [fieldValue,fieldValue,InternalEqualityTestEvaluationProof.vectorTwo]
  exact InternalEqualityTestEvaluationProof.exactEqualityEvaluation _ _

theorem edgeCalibration (n : Nat) (arity : Fin n → Nat) (B : Program 3)
    (hB : ∀ v, evaluate B v = structuralValue n arity v) :
    ∀ v, evaluate (edge B) v = TransparentPrimary.edgeValue n arity v := by
  intro v
  rw [edge,InternalAcceptanceCalibrationProof.actualConjunctionEvaluation,guardValue,hB]
  cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (Nat.unpair (v.get 2)).1 with
  | none => simp only [structuralValue,TransparentPrimary.edgeValue,hc]
    simp
  | some ctx =>
    cases ha : Encodable.decode (α := RawPacked n) (v.get 0) with
    | none => simp only [structuralValue,TransparentPrimary.edgeValue,hc,ha]
      simp
    | some a =>
      cases hb : Encodable.decode (α := RawPacked n) (v.get 1) with
      | none => simp only [structuralValue,TransparentPrimary.edgeValue,hc,ha,hb]
        simp
      | some b =>
        have ea := decodedTypeField n (v.get 0) a ha
        have eb := decodedTypeField n (v.get 1) b hb
        have ht : (Nat.unpair (v.get 0)).1 = (Nat.unpair (v.get 1)).1 ↔ a.1 = b.1 := by
          rw [← ea,← eb]
          exact Encodable.encode_injective.eq_iff
        simp only [structuralValue,TransparentPrimary.edgeValue,hc,ha,hb,NumberedExchangeCode.packedCodeExchange]
        rw [ht]
        by_cases he : a.1 = b.1 <;>
          cases hx : NumberedExchangeCode.codeExchange arity ctx.1.1 ctx.1.2 a.2 b.2 <;>
          simp [he,hx]

theorem selectedTuple : Targets.SelectedTuple := by
  intro n arity p H G W hp hH hG hW
  obtain ⟨Q,hQ⟩ := Proof.allPrimitiveFunctions 2 _ (SeededPrimaryPool.NativeProof.candidatesValuePrimitive n arity)
  obtain ⟨B,hB⟩ := Proof.allPrimitiveFunctions 3 _ (structuralPrimitive n arity)
  let T := OriginalTypedDecoder.target H G
  let P := SeededPrimaryPool.pool T Q
  have hT := OriginalTypedDecoderTargetLeafProof.actualOriginalTypedTargetLeafCalibration n arity H G hH hG
  have hP := SeededPrimaryPool.NativeProof.poolCalibration n arity T Q hT hQ
  have hs : TransparentPrimary.SuppliersCalibrated n arity (LengthAlignedPrimary.countOfPool P) P (edge B) :=
    ⟨LengthAlignedPrimary.NativeProof.countCalibration n arity P hP,hP,edgeCalibration n arity B hB⟩
  have hL := TransparentPrimary.NativeProof.calibration n arity T (LengthAlignedPrimary.countOfPool P) P (edge B) hT hs
  have hr := CandidateIntegration.Proof.retainedTuple n arity p H G W
    (SeededPrimaryPool.primary T Q (edge B)) hp hH hG hW hL
  exact ⟨Q,B,hQ,hB,hs,hL,hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TypedPrimaryEdge.NativeProof
