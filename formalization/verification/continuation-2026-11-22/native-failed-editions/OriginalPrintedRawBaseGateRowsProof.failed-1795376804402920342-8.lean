module
public import LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRowsTargets
import LogicLineages.PermittedControl.ArbitraryHeadSharedWireTypedProof
import LogicLineages.OrdinalComparison.RawNotationCode
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRows
open OrdinalComparison
open FieldComparison (longFieldCode)
open OriginalNormalizedCircuitMatrix (affineRows limitRows LimitHead typedHead baseRows rows rowsList)
open HeterogeneousSignedMatrixSlice (encodeRow encodeTest)
open MixedSameRankResidue (encodeWeighted)
open PreparedProjection (LowerOperand)
open NaturalAffineGateGraph (Expression)
open ArbitraryHeadSharedWire (headCode limitCode tailCode finiteExpression shiftedExpression exactTypedWireTransport)
open ArbitraryHeadWireList (normalizeGate)
open ArbitraryHeadFreshWireAllocation (install)
open OriginalPrintedCircuitNumericRead (encodeGate)

private theorem literalAffine (e : Expression) (out : Nat) :
    affineEqualityCode (e,out) =
      encodeRow (.equalZero,e.1,AffineCollapseGuardRows.affineTerms e out) := by
  simp only [affineEqualityCode,encodeRow,encodeTest,AffineCollapseGuardRows.affineTerms,
    List.map_cons,List.map_map,Function.comp_def] <;> rfl

theorem exactBaseRawAffine : ExactBaseRawAffine := by
  intro e out
  exact congrArg (fun r => [r]) (literalAffine e out)

private theorem normLiteral (a : NONote) :
    rawNormCode (rawNoteEncode a.1) = actualOrdinalNorm a.1.repr := by
  rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence a]

theorem exactBaseRawNormLimit : ExactBaseRawNormLimit := by
  intro head e input output good
  let a := typedHead head good
  have code : rawNoteEncode a.1 = head := rawNoteEncodeDecode head
  have norm : rawNormCode head = actualOrdinalNorm a.1.repr := by
    rw [← code,normLiteral]
  rw [limitRows,dif_pos good]
  change [affineEqualityCode (e,input),normGuardCode head input,
      collapseEqualityCode head input output] =
    (AffineCollapseGuardRows.guardRows a e input output).map encodeRow
  simp only [AffineCollapseGuardRows.guardRows,List.map_cons,List.map_nil,← literalAffine]
  simp [normGuardCode,collapseEqualityCode,AffineCollapseGuardRows.collapseTerms,
    encodeRow,encodeTest,encodeWeighted,LowerOperand.code,longFieldCode,coordinateCode,zeroCode,norm,code]

theorem exactOriginalRawBaseGateStep : ExactOriginalRawBaseGateStep := by
  intro g n
  cases g with
  | affine e out =>
    change some (n,[affineEqualityCode (e,out)]) = some (n,(affineRows e out).map encodeRow)
    rw [exactBaseRawAffine]
  | collapse w =>
    rcases w with ⟨a,source,output⟩
    let wire : ArbitraryHeadFreshWireAllocation.Wire := ⟨a,source,output⟩
    simp only [OriginalPrintedCircuitNormalization.normalizeFrom,rowsList,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,rows]
    change some (n+1,collapseRowsCode (headCode a,source,n,output)) =
      some (n+1,(baseRows (normalizeGate (install wire n))).map encodeRow)
    cases kind : encodedFiniteTest (headCode a) with
    | true =>
      have lhs : collapseRowsCode (headCode a,source,n,output) =
          [affineEqualityCode (finiteExpression a source,output)] := by
        simp [collapseRowsCode,finiteExpression,kind]
      have rhs : baseRows (normalizeGate (install wire n)) = affineRows (finiteExpression a source) output := by
        simp [normalizeGate,ArbitraryHeadWireList.Gate.finite,install,wire,kind,baseRows]
      rw [lhs,rhs,exactBaseRawAffine]
    | false =>
      obtain ⟨lam,code,limit,_,_,_,_,_⟩ := exactTypedWireTransport.1 a 0 kind
      have good : LimitHead (limitCode a) := by
        rw [← code]
        simpa only [LimitHead,rawNoteDecodeEncode] using (And.intro lam.2 limit)
      have lhs : collapseRowsCode (headCode a,source,n,output) =
          limitRowsCode (limitCode a,shiftedExpression a source,n,output) := by
        simp [collapseRowsCode,limitCode,tailCode,shiftedExpression,kind]
      have rhs : baseRows (normalizeGate (install wire n)) =
          limitRows (limitCode a) (shiftedExpression a source) n output := by
        simp [normalizeGate,ArbitraryHeadWireList.Gate.finite,install,wire,kind,baseRows]
      rw [lhs,rhs,exactBaseRawNormLimit _ _ _ _ good]

end LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRows
