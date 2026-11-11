module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedAuxiliaryBetaPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesPrimitiveProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultPrimitiveProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedUniformPackedDecoding NumberedAuxiliarySubstitution OriginalBetaResult

attribute [local irreducible] Primrec

/-- Primitive recursion is joint in Gamma and the original raw source. The
encoding step explicitly uses the checked typeNumber/codeNumber suppliers. -/
theorem rawResultPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : List Ty × Nat => rawResult n arity p.1 p.2) := by
  let Input := (List Ty × Nat) × RawPacked n
  have hd : Primrec (fun p : List Ty × Nat => rawPackedDecode n arity p.1 p.2) :=
    NumberedUniformPackedDecodingProof.rawPackedDecoderPrimitive n arity
  have hf : Primrec (fun p : Input => p.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hb : Primrec (fun p : Input => betaCode p.1.1.length p.2.2) :=
    (NumberedAuxiliaryBetaPrimrecProof.allBetaCodePrimitive n).comp hf
      (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : Input × Code (Fin n) => typeNumber p.1.2.1) :=
    NumberedTypeCodecPrimrecProof.typeEncoderPrimitive.comp
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hc : Primrec (fun p : Input × Code (Fin n) => codeNumber p.2) :=
    (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n).comp Primrec.snd
  have he : Primrec (fun p : Input × Code (Fin n) =>
      Nat.succ (Nat.pair (typeNumber p.1.2.1) (codeNumber p.2))) :=
    Primrec.succ.comp (Primrec₂.natPair.comp ht hc)
  have hm : Primrec (fun p : Input =>
      (betaCode p.1.1.length p.2.2).map (fun code =>
        Nat.succ (Nat.pair (typeNumber p.2.1) (codeNumber code)))) :=
    Primrec.option_map hb he.to₂
  exact Primrec.option_getD.comp (Primrec.option_bind hd hm.to₂) (Primrec.const 0)

theorem actualOriginalBetaResultPrimitive :
    OriginalBetaResultTargets.ActualOriginalBetaResultPrimitive := by
  intro n arity
  apply InternalOriginalUniformParameterLeavesPrimitiveProof.decodedValuePrimitive n
    (fun p => rawResult n arity p.2.1 p.2.2)
  exact (rawResultPrimitive n arity).comp Primrec.snd

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultPrimitiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultPrimitiveProof
