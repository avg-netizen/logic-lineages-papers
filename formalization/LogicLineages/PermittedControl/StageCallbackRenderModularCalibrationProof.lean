module
public import LogicLineages.PermittedControl.StageCallbackRenderModularTargets
import LogicLineages.PermittedControl.StageCallbackRenderLinearCalibrationProof
import LogicLineages.PermittedControl.MixedRankNamedResidueRowSyntaxCodeProof
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode)
open RawPacketAlgebra (encodePacket)
open MixedSameRankResidue (WeightedOperand WeightedCode encodeWeighted)
open MixedRankResidue (rankSupport rankSupportCode residueVector residueVectorCode)
open RankResidueChoices (Slot Cell namedSlots choices)
open MixedRankNamedResidueRow (RawArgs rowFrom toVector clauseCode clauseCodeLiteral)
open MixedNamedResidueRow (keep)
open SharedRankResidueRow (Layout formula formulaCode)
open StatementChecks (fixed_mixedRankResidueCodeExact)
open ActualGreatestCongruenceRoute (lowerRanks)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualSymbolicZeroSuccessor (SyntaxState)
open OriginalMatrixLinearRowFormula (choosePolarity)

theorem foldFilter (top : Nat) (l : List Nat) :
    l.foldr (fun rank rest => if rank < top then rank :: rest else rest) [] =
      l.filter (fun rank => decide (rank < top)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show (if a < top then
        a :: l.foldr (fun rank rest => if rank < top then rank :: rest else rest) []
      else l.foldr (fun rank rest => if rank < top then rank :: rest else rest) []) = _
    rw [ih]
    by_cases h : a < top
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      simp [h]

theorem lowerRanksExact (top : Nat) (ts : List WeightedOperand) :
    lowerRanksCode top (ts.map encodeWeighted) = lowerRanks top ts := by
  show (rankSupportCode (ts.map encodeWeighted)).foldr
      (fun rank rest => if rank < top then rank :: rest else rest) [] =
    (rankSupport ts).filter (fun rank => decide (rank < top))
  rw [fixed_mixedRankResidueCodeExact.2.2.1,foldFilter]

/-- The accepted residue-row formula code is literal for every modulus. -/
theorem formulaExact (layout : Layout) (m : Nat) (c : Int) (ts : List WeightedOperand) :
    formulaCode layout (m,c,ts.map encodeWeighted) = (formula layout (m,c,ts)).encode := by
  simp only [formulaCode,formula,rowFrom,fixed_mixedRankResidueCodeExact.2.2.2,clauseCodeLiteral]
  generalize choices m layout = cells
  induction cells with
  | nil => rfl
  | cons cell tail ih =>
    simp only [List.foldr_cons]
    by_cases selected : keep m (c+residueVector ts (toVector cell)) = true
    · simp only [if_pos selected,NormalForm.Formula.encode,ih]
    · simp only [if_neg selected,ih]

theorem exactModularCode : ExactModularCode := by
  intro top m s positive
  have tableEq : (lowerRanks top s.terms).map coordinateCode =
      ((lowerRanks top s.terms).map LowerOperand.coordinate).map LowerOperand.code := by
    simp [List.map_map,Function.comp_def,LowerOperand.code,coordinateCode]
  show (Encodable.encode ((lowerRanksCode top (s.terms.map encodeWeighted)).map coordinateCode),
      polarityCode (formulaCode
        ((0,top) :: namedSlots (lowerRanksCode top (s.terms.map encodeWeighted)))
        (m,s.constant,s.terms.map encodeWeighted)) positive) =
    (Encodable.encode (((lowerRanks top s.terms).map LowerOperand.coordinate).map
        LowerOperand.code),
      (choosePolarity (formula ((0,top) :: namedSlots (lowerRanks top s.terms))
        (m,s.constant,s.terms)) positive).encode)
  rw [lowerRanksExact,formulaExact,polarityExact,tableEq]

end LogicLineages.PermittedControl.StageCallbackRender
