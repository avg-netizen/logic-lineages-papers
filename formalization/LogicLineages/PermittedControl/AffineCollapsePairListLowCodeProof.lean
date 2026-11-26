module
public import LogicLineages.PermittedControl.AffineCollapsePairListLowTargets
import LogicLineages.PermittedControl.AffineCollapseGuardedLowCodeProof
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsCodeProof
import LogicLineages.OrdinalComparison.ActualOrdinalNorm
import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapsePairListLow
open OrdinalComparison PreparedProjection FieldComparison
open AffineCollapseGuardedLow (PairData guardRowsCode coordinateCode)
open MixedSameRankResidue (encodeWeighted)
open HeterogeneousSignedMatrixSlice (RawRow encodeRow encodeTest)
open HeterogeneousSignedMatrixLowStrips (branchesCode)

private theorem oneCode (p : Pair) :
    guardRowsCode (encodePair p) =
      (AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2).map encodeRow := by
  have norm : rawNormCode (rawNoteEncode p.1.1) = actualOrdinalNorm p.1.1.repr :=
    (rawNormCodeCorrect p.1.1).trans (actualOrdinalNorm_notationCorrespondence p.1).symm
  simp only [encodePair,guardRowsCode,norm,AffineCollapseGuardRows.guardRows,
    AffineCollapseGuardRows.affineTerms,AffineCollapseGuardRows.collapseTerms,
    List.map_cons,List.map_nil,encodeRow,encodeTest,List.map_map,Function.comp_def,
    encodeWeighted,LowerOperand.code,longFieldCode,AffineCollapseGuardRows.zeroTarget,
    rawNoteEncode,coordinateCode] <;> rfl

private theorem prefixCalibrated (pairs : List Pair) :
    prefixCode (pairs.map encodePair) = (prefixRows pairs).map encodeRow := by
  induction pairs with
  | nil => rfl
  | cons p ps ih =>
      change guardRowsCode (encodePair p) ++ prefixCode (ps.map encodePair) =
        (AffineCollapseGuardRows.guardRows p.1 p.2.1 p.2.2.1 p.2.2.2 ++ prefixRows ps).map encodeRow
      rw [oneCode,ih,List.map_append]

private theorem prefixPrimitive : Primrec prefixCode := by
  let Env := List PairData × (PairData × List RawRow)
  have ctx : Primrec (Prod.snd : Env → PairData × List RawRow) := Primrec.snd
  have rows : Primrec (fun p : Env => guardRowsCode p.2.1) :=
    AffineCollapseGuardedLow.exactPairBranchCode.1.comp (Primrec.fst.comp ctx)
  have rest : Primrec (fun p : Env => p.2.2) := Primrec.snd.comp ctx
  exact Primrec.list_foldr Primrec.id (Primrec.const ([] : List RawRow))
    (Primrec.list_append.comp rows rest).to₂

theorem exactListBranchCode : ExactListBranchCode := by
  refine ⟨prefixPrimitive,?_,?_,?_⟩
  · intro f hf
    have first : Primrec (Prod.fst : Args → Nat) := Primrec.fst
    have rest : Primrec (Prod.snd : Args → Nat × List PairData × List RawRow) := Primrec.snd
    have bound : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp rest
    have both : Primrec (fun p : Args => p.2.2) := Primrec.snd.comp rest
    have g := prefixPrimitive.comp (Primrec.fst.comp both)
    have tail : Primrec (fun p : Args => p.2.2.2) := Primrec.snd.comp both
    have combine : Primrec (fun p : Args => (p.1,p.2.1,prefixCode p.2.2.1 ++ p.2.2.2)) :=
      first.pair (bound.pair (Primrec.list_append.comp g tail))
    exact (HeterogeneousSignedMatrixLowStrips.codeExact.1 f hf).comp combine.to_comp
  · intro f p
    exact HeterogeneousSignedMatrixLowStrips.codeExact.2.1 f
      (p.1,p.2.1,prefixCode p.2.2.1 ++ p.2.2.2)
  · intro f pairs rank bound testRows
    change branchesCode f (rank,bound,prefixCode (pairs.map encodePair) ++ testRows.map encodeRow) = _
    rw [prefixCalibrated,← List.map_append]
    exact HeterogeneousSignedMatrixLowStrips.codeExact.2.2 f rank bound _

end LogicLineages.PermittedControl.AffineCollapsePairListLow
