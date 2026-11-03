module
public import LogicLineages.OrdinalComparison.CommonHeadSmallFoldTargets
public import LogicLineages.OrdinalComparison.RawNormCode
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.CommonHeadSmallFold.Proof

private theorem evaluator_computable : Computable₂ closedValueCode :=
  encodedCollapseComputable.comp (encodedFiniteTailPrimitiveRecursive.comp Primrec.fst
    (Primrec.nat_sub.comp Primrec.snd
      ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp Primrec.fst))).to_comp

private theorem norm_exact (rho : NONote) :
    rawNormCode (rawNoteEncode rho.1)=actualOrdinalNorm rho.1.repr := by
  rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence rho]

theorem closedEvaluation : Targets.ClosedEvaluation := by
  refine ⟨evaluator_computable,?_⟩
  intro rho c
  refine ⟨?_,?_⟩
  · unfold closedValueCode
    rw [(encodedFiniteTailCorrect rho _).1,encodedCollapseSourceCorrect,
      (finiteTailCorrect rho _).1,norm_exact rho]
    rfl
  · intro K row
    simp only [smallValuesCode,smallValues,norm_exact rho]
end LogicLineages.OrdinalComparison.CommonHeadSmallFold.Proof
