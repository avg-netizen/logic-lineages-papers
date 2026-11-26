module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesCodecProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open InternalOriginalUniformParameterLeaves

/-- Preserve the ORIGINAL packed decoder's final round-trip filter. The
variable decoder's soundness pays that filter at its successful outputs. -/
theorem variablePackedDecode (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (tau : Ty) (index : Nat) :
    decodePackedNumber n arity Gamma (Nat.pair (typeNumber tau) (Nat.pair 0 index)) =
      (decodeVariable Gamma tau index).map
        (fun v => (⟨tau,AuxTerm.var v⟩ : Packed (Fin n) arity Gamma)) := by
  have hc : decodeCode n (Nat.pair 0 index) = some (.var index) :=
    NumberedNumericDecodingProof.codeRoundTrip n (.var index)
  cases hv : decodeVariable Gamma tau index with
  | none =>
    simp [decodePackedNumber,packedParse,Nat.unpair_pair,
      NumberedNumericDecodingSupportProof.typeRoundTrip,hc,decodePacked,decodeTerm,hv]
  | some v =>
    have hi := NumberedAuxiliaryDecodingProof.variableSound Gamma tau index v hv
    simp [decodePackedNumber,packedParse,Nat.unpair_pair,
      NumberedNumericDecodingSupportProof.typeRoundTrip,hc,decodePacked,decodeTerm,hv,
      packedNumber,termCode,codeNumber,hi]

/-- The source's original universe filter tests precisely the variable's
actual type, without any closure or precedence premise. -/
theorem variableSourceValue (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (tau : Ty) (index : Nat) :
    InternalOriginalStepGuard.sourceValidityValue n arity symbols S Gamma
      (Nat.pair (typeNumber tau) (Nat.pair 0 index)) =
        ((decide (tau ∈ S)) && (decodeVariable Gamma tau index).isSome).toNat := by
  cases hv : decodeVariable Gamma tau index <;>
    simp [InternalOriginalStepGuard.sourceValidityValue,
      rawCarrierTest,decodeUniverse,variablePackedDecode,hv,universeTest]

/-- The existing rawPackedDecode bridge is used later through decodedLeafSlice;
this is its original numeric typed decoder on the actual variable constructor. -/
theorem variableTargetValue (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (tau : Ty) (index : Nat) :
    InternalOriginalStepGuard.targetValidityValue n arity Gamma
      (Nat.pair (typeNumber tau) (Nat.pair 0 index)) =
        (decodeVariable Gamma tau index).isSome.toNat := by
  simp only [InternalOriginalStepGuard.targetValidityValue,
    variablePackedDecode,Option.isSome_map]

/-- Every original parameter Gamma has its original Encodable code, not the
separate raw typesNumber list code. This is the actual Object-code inverse. -/
theorem parameterGammaCode (parameter : Nat) :
    ∃ Gamma : List Ty,
      Encodable.encode Gamma = (Nat.unpair parameter).2 ∧
      ∀ value : Nat, parameterObject value parameter = some (Gamma,value) := by
  obtain ⟨Gamma,ho⟩ := BottomRepresentativeEvaluationProof.parameterGamma parameter
  have he := (JointGammaDomainCodecProof.actualObjectCodec.2.1
    (Nat.pair (Nat.unpair parameter).2 0) (Gamma,0)).mp (ho 0)
  have hg : Encodable.encode Gamma = (Nat.unpair parameter).2 := by
    have h := congrArg (fun k : Nat => (Nat.unpair k).1) he
    simpa only [ContextUniform.objectCode,Encodable.encode_prod_val,
      Encodable.encode_nat,Nat.unpair_pair] using h
  exact ⟨Gamma,hg,ho⟩

/-- Raw tag zero has exactly the original packed variable constructor, even
before typedness succeeds. The original type decoder is total on all codes. -/
theorem variableRawShape (raw : Nat)
    (h : (Nat.unpair (Nat.unpair raw).2).1 = 0) :
    ∃ tau : Ty,
      typeNumber tau = (Nat.unpair raw).1 ∧
      raw = Nat.pair (typeNumber tau) (Nat.pair 0 (Nat.unpair (Nat.unpair raw).2).2) := by
  obtain ⟨tau,_,ht⟩ := NumberedTypeCodecTotalProof.typeDecoderTotal (Nat.unpair raw).1
  refine ⟨tau,ht,?_⟩
  rw [ht,← h,Nat.pair_unpair,Nat.pair_unpair]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesCodecProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeavesCodecProof
