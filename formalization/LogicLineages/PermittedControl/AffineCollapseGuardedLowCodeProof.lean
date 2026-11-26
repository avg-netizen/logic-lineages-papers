module
public import LogicLineages.PermittedControl.AffineCollapseGuardedLowTargets
import LogicLineages.PermittedControl.HeterogeneousSignedMatrixLowStripsCodeProof
import LogicLineages.OrdinalComparison.ActualOrdinalNorm
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseGuardedLow
open OrdinalComparison PreparedProjection FieldComparison
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open AffineCollapseGraphComposition (Expression)
open MixedSameRankResidue (WeightedCode encodeWeighted)
open HeterogeneousSignedMatrixSlice (RawRow encodeRow encodeTest)
open HeterogeneousSignedMatrixLowStrips (branchesCode)

private theorem coordinatePrimitive : Primrec coordinateCode :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const (0,0,0,0)))

private theorem guardPrimitive : Primrec guardRowsCode := by
  let Occ := PairData × (Int × Nat)
  have head : Primrec (fun p : PairData => p.1) := Primrec.fst
  have expr : Primrec (fun p : PairData => p.2.1) := Primrec.fst.comp Primrec.snd
  have io : Primrec (fun p : PairData => p.2.2) := Primrec.snd.comp Primrec.snd
  have input : Primrec (fun p : PairData => p.2.2.1) := Primrec.fst.comp io
  have output : Primrec (fun p : PairData => p.2.2.2) := Primrec.snd.comp io
  have occ : Primrec (Prod.snd : Occ → Int × Nat) := Primrec.snd
  have weighted : Primrec (fun p : Occ => (p.2.1,coordinateCode p.2.2)) :=
    (Primrec.fst.comp occ).pair (coordinatePrimitive.comp (Primrec.snd.comp occ))
  have ts : Primrec (fun p : PairData => p.2.1.2.map (fun t => (t.1,coordinateCode t.2))) :=
    Primrec.list_map (Primrec.snd.comp expr) weighted.to₂
  have a0 := (Primrec.const (-1 : Int)).pair (coordinatePrimitive.comp input)
  have ats := Primrec.list_cons.comp a0 ts
  have row1 : Primrec (fun p : PairData => (((0,0),p.2.1.1,
      (-1,coordinateCode p.2.2.1) :: p.2.1.2.map (fun t => (t.1,coordinateCode t.2))) : RawRow)) :=
    (Primrec.const (0,0)).pair ((Primrec.fst.comp expr).pair ats)
  have norm : Primrec (fun p : PairData => -(rawNormCode p.1 : Int)) :=
    negate_primitive.comp (ofNat_primitive.comp ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp head))
  have nt : Primrec (fun p : PairData => ([(1,coordinateCode p.2.2.1)] : List WeightedCode)) :=
    Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (coordinatePrimitive.comp input))
      (Primrec.const [])
  have row2 : Primrec (fun p : PairData => (((1,0),-(rawNormCode p.1 : Int),
      [(1,coordinateCode p.2.2.1)]) : RawRow)) := (Primrec.const (1,0)).pair (norm.pair nt)
  have endpoints : Primrec (fun p : PairData => ((1,0,p.1,0) : LongFieldCode)) :=
    (Primrec.const 1).pair ((Primrec.const 0).pair (head.pair (Primrec.const 0)))
  have endpoint := input.pair endpoints
  have v : Primrec (fun p : PairData => ((1,(1,p.2.2.1,(1,0,p.1,0))) : WeightedCode)) :=
    (Primrec.const (1 : Int)).pair ((Primrec.const 1).pair endpoint)
  have k : Primrec (fun p : PairData => ((1,(2,p.2.2.1,(1,0,p.1,0))) : WeightedCode)) :=
    (Primrec.const (1 : Int)).pair ((Primrec.const 2).pair endpoint)
  have ot := (Primrec.const (-1 : Int)).pair (coordinatePrimitive.comp output)
  have cts := Primrec.list_cons.comp ot (Primrec.list_cons.comp v
    (Primrec.list_cons.comp k (Primrec.const ([] : List WeightedCode))))
  have row3 : Primrec (fun p : PairData => (((0,0),0,
      [(-1,coordinateCode p.2.2.2),(1,(1,p.2.2.1,(1,0,p.1,0))),
        (1,(2,p.2.2.1,(1,0,p.1,0)))]) : RawRow)) :=
    (Primrec.const (0,0)).pair ((Primrec.const (0 : Int)).pair cts)
  exact Primrec.list_cons.comp row1 (Primrec.list_cons.comp row2
    (Primrec.list_cons.comp row3 (Primrec.const ([] : List RawRow))))

private theorem guardCodeCalibration (lam : NONote) (e : Expression) (input output : Nat) :
    guardRowsCode (rawNoteEncode lam.1,e,input,output) =
      (AffineCollapseGuardRows.guardRows lam e input output).map encodeRow := by
  have norm : rawNormCode (rawNoteEncode lam.1) = actualOrdinalNorm lam.1.repr :=
    (rawNormCodeCorrect lam.1).trans (actualOrdinalNorm_notationCorrespondence lam).symm
  simp only [guardRowsCode,norm,AffineCollapseGuardRows.guardRows,AffineCollapseGuardRows.affineTerms,
    AffineCollapseGuardRows.collapseTerms,List.map_cons,List.map_nil,encodeRow,encodeTest,
    List.map_map,Function.comp_def,encodeWeighted,LowerOperand.code,longFieldCode,
    AffineCollapseGuardRows.zeroTarget,rawNoteEncode,coordinateCode] <;> rfl

theorem exactPairBranchCode : ExactPairBranchCode := by
  refine ⟨guardPrimitive,?_,?_,?_⟩
  · intro f hf
    have first : Primrec (Prod.fst : Args → Nat) := Primrec.fst
    have rest : Primrec (Prod.snd : Args → Nat × PairData × List RawRow) := Primrec.snd
    have bound : Primrec (fun p : Args => p.2.1) := Primrec.fst.comp rest
    have both : Primrec (fun p : Args => p.2.2) := Primrec.snd.comp rest
    have g := guardPrimitive.comp (Primrec.fst.comp both)
    have tail : Primrec (fun p : Args => p.2.2.2) := Primrec.snd.comp both
    have combine : Primrec (fun p : Args =>
        (p.1,p.2.1,guardRowsCode p.2.2.1 ++ p.2.2.2)) :=
      first.pair (bound.pair (Primrec.list_append.comp g tail))
    exact (HeterogeneousSignedMatrixLowStrips.codeExact.1 f hf).comp combine.to_comp
  · intro f p
    exact HeterogeneousSignedMatrixLowStrips.codeExact.2.1 f
      (p.1,p.2.1,guardRowsCode p.2.2.1 ++ p.2.2.2)
  · intro f lam e input output rank bound testRows
    change branchesCode f
      (rank,bound,guardRowsCode (rawNoteEncode lam.1,e,input,output) ++ testRows.map encodeRow) = _
    rw [guardCodeCalibration,← List.map_append]
    exact HeterogeneousSignedMatrixLowStrips.codeExact.2.2 f rank bound _

end LogicLineages.PermittedControl.AffineCollapseGuardedLow
