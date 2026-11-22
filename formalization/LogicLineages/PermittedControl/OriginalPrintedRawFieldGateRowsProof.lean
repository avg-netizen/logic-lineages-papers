module
public import LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRowsTargets
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.ActualOrdinalNorm

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (encodeRow encodeTest)
open OriginalPrintedCircuitNumericRead (encodeGate)
open OriginalPrintedRawBaseGateRows (coordinateCode normGuardCode)
open OriginalFieldGateMatrix (equalityRow zeroRow identityShapeRow identityAffordRow)
open PreparedProjection (LowerOperand)
open MixedSameRankResidue (encodeWeighted)

private theorem normLiteral (a : NONote) :
    rawNormCode (rawNoteEncode a.1) = actualOrdinalNorm a.1.repr := by
  rw [rawNormCodeCorrect,actualOrdinalNorm_notationCorrespondence a]

private theorem identityNormLiteral (mu : NONote) (source : Nat) :
    normGuardCode (rawNoteEncode mu.1) source = encodeRow (identityAffordRow mu source) := by
  simp [normGuardCode,identityAffordRow,encodeRow,encodeTest,encodeWeighted,coordinateCode,
    LowerOperand.code,normLiteral]

theorem exactOriginalRawFieldGateRows : ExactOriginalRawFieldGateRows := by
  intro g
  cases g with
  | iterate steps source output => rfl
  | entry int source output =>
    cases int with
    | proper lam mu => rfl
    | identity mu =>
      change some (identityRowsCode false (rawNoteEncode mu.1) source output) =
        some ([identityShapeRow mu,identityAffordRow mu source,
          equalityRow (.coordinate source) output].map encodeRow)
      simp only [identityRowsCode,List.map_cons,List.map_nil,← identityNormLiteral] <;> rfl
  | count int source output =>
    cases int with
    | proper lam mu => rfl
    | identity mu =>
      change some (identityRowsCode true (rawNoteEncode mu.1) source output) =
        some ([identityShapeRow mu,identityAffordRow mu source,zeroRow output].map encodeRow)
      simp only [identityRowsCode,List.map_cons,List.map_nil,← identityNormLiteral] <;> rfl

theorem exactOriginalRawFieldGateStep : ExactOriginalRawFieldGateStep := by
  intro g n
  rw [stepCode,exactOriginalRawFieldGateRows]
  simp only [OriginalPrintedCircuitNormalization.normalizeFrom,OriginalNormalizedCircuitMatrix.rowsList,
    OriginalNormalizedCircuitMatrix.rows,List.flatMap_cons,List.flatMap_nil,List.append_nil] <;> rfl

end LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
