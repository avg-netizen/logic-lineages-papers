module
public import LogicLineages.PermittedControl.ActualBitFamilyRawRankTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawRank
open PreparedProjection (LowerOperand LowerOperandCode)
open MixedSameRankResidue (WeightedCode encodeWeighted)
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalPrintedTerminalBitClauses (BitRow)
open ActualFiniteOrderBranches (Pattern rename)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily occurrences)
open OriginalMatrixLowDimensionCode (rawSupport)
open OriginalMatrixDenseRanks (renameOperand renameTerm renameRow)
open ActualBitFamilyHigh (renameBit ranked)

private theorem literalOperand (p : Pattern) (op : LowerOperand) :
    operandCode p op.code = (renameOperand (rename p) op).code := by
  cases op <;> rfl

private theorem literalBit (p : Pattern) (r : BitRow) :
    bitCode p (encodeBitRow r) = encodeBitRow (renameBit p r) := by
  have termEq (t : MixedSameRankResidue.WeightedOperand) :
      termCode p (encodeWeighted t) = encodeWeighted (renameTerm (rename p) t) :=
    congrArg (Prod.mk t.1) (literalOperand p t.2)
  have literalTerms (terms : List MixedSameRankResidue.WeightedOperand) :
      (terms.map encodeWeighted).map (termCode p) =
        (terms.map (renameTerm (rename p))).map encodeWeighted := by
    simp only [List.map_map,Function.comp_def,termEq]
  change ((HeterogeneousSignedMatrixSlice.encodeTest r.1.1,r.1.2.1,(r.1.2.2.map encodeWeighted).map (termCode p)),r.2) =
    ((HeterogeneousSignedMatrixSlice.encodeTest r.1.1,r.1.2.1,
      (r.1.2.2.map (renameTerm (rename p))).map encodeWeighted),r.2)
  rw [literalTerms]

theorem exactRawRankCalibration : ExactRawRankCalibration := by
  intro p family
  have rowList (clause : List BitRow) :
      (clause.map encodeBitRow).map (bitCode p) = (clause.map (renameBit p)).map encodeBitRow := by
    simp only [List.map_map,Function.comp_def,literalBit]
  simp only [familyCode,encodeFamily,ranked,List.map_map,Function.comp_def,rowList]

private theorem literalMetadata (p : Pattern) (r : RawBitRow) :
    metadata (bitCode p r) = metadata r := by
  simp only [metadata,bitCode,rowCode,List.map_map,Function.comp_def,termCode,operandCode]

private theorem rawRenamedSupport (p : Pattern) (rows : List RawRow) :
    rawSupport (rows.map (rowCode p)) = (rawSupport rows).map (rename p) := by
  induction rows with
  | nil => rfl
  | cons row tail ih =>
      change ((row.2.2.map (termCode p)).map (fun t => t.2.2.1)) ++
          rawSupport (tail.map (rowCode p)) =
        ((row.2.2.map (fun t => t.2.2.1)) ++ rawSupport tail).map (rename p)
      simp only [List.map_append,List.map_map,Function.comp_def,termCode,operandCode,rankCode,ih]

theorem exactRawRankLiteralShape : ExactRawRankLiteralShape := by
  intro p raw
  refine ⟨?_,?_⟩
  · simp only [familyCode,List.map_map,Function.comp_def,literalMetadata]
  · have flat :
        (familyCode (p,raw)).flatMap (List.map Prod.fst) =
          (raw.flatMap (List.map Prod.fst)).map (rowCode p) := by
        induction raw with
        | nil => rfl
        | cons head tail ih =>
            change ((head.map (bitCode p)).map Prod.fst) ++
                (familyCode (p,tail)).flatMap (List.map Prod.fst) =
              (head.map Prod.fst ++ tail.flatMap (List.map Prod.fst)).map (rowCode p)
            simp only [List.map_append,List.map_map,Function.comp_def,bitCode,ih]
    unfold occurrences
    rw [flat,rawRenamedSupport]

end LogicLineages.PermittedControl.ActualBitFamilyRawRank
