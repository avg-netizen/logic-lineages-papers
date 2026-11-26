module
public import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthTargets
import LogicLineages.PermittedControl.ActualCanonicalTerminalTruthLinearProof
import LogicLineages.PermittedControl.ActualCanonicalNormalizedTapeProof
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingReadProof
import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalCalibrationProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsAlgebraProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PlainPreparedRow PreparedInput PreparedTableTied lowerOperandRead)
open ActualZeroClassReplacement (Read readSum liftedReads)
open ActualWeightedReadNormalization (exactNormalizedReads normalizeReads)
open ActualLinearExit (lowerReads table exitRow OriginalSlots replay)
open ActualSyntaxLinearTerminal (termsTable termsRow exactSyntaxOfLinearExit)
open ActualCanonicalOperandGrouping ActualCanonicalNormalizedTape
open ActualReadChargeIteration (ActiveAt)
open OriginalMatrixLinearRowFormula (testFormula choosePolarity safeTest safePolarity)
open SignedRowGuardedTest (Test)

private theorem testMeaning (test : Test) (row : NormalForm.Row) (ν : Nat → Nat) (adm : test.Admitted) :
    (testFormula test row).eval ν ↔ test.Holds (NormalForm.rowValue row ν) := by
  cases test with
  | equalZero =>
      change (0 ≤ NormalForm.rowValue row ν ∧ 0 ≤ NormalForm.rowValue (LinearRows.rowScale (-1) row) ν) ↔
        NormalForm.rowValue row ν = 0
      rw [LinearRowsSemanticProof.rowScale_value]
      omega
  | nonnegative => rfl
  | positive =>
      let total : Int := (row.2.map (fun a => a.1 * (a.2.term.value ν : Int))).sum
      change 0 ≤ row.1 - 1 + total ↔ 0 < row.1 + total
      omega
  | congruence m =>
      have pos : 0 < m := adm
      have exactM : m-1+1 = m := by omega
      change (((m-1+1 : Nat) : Int) ∣ NormalForm.rowValue row ν) ↔
        (m : Int) ∣ NormalForm.rowValue row ν
      rw [exactM]

private theorem boolMeaning (test : Test) (row : NormalForm.Row) (ν : Nat → Nat)
    (adm : test.Admitted) (positive : Bool) :
    (choosePolarity (testFormula test row) positive).eval ν ↔
      test.atPolarity positive (NormalForm.rowValue row ν) := by
  cases positive with
  | true => exact testMeaning test row ν adm
  | false => exact not_congr (testMeaning test row ν adm)

theorem exactCanonicalInactiveTruth : ExactCanonicalInactiveTruth := by
  intro f ρ top constant rs xs live bounded normal inactive test positive adm
  have tape := exactCanonicalTapeCertificate f ρ rs xs live normal
  obtain ⟨old,legacy,_,_,_,_,_⟩ := (exactNormalizedReads f ρ rs).2 live
  obtain ⟨out,found,_,tapeEq,_,_⟩ := (exactCanonicalReads f ρ rs).2 old legacy
  have same : out = xs := Option.some.inj (found.symm.trans normal)
  have terms : xs.map Prod.fst = groupTyped (rs.map Prod.fst) :=
    (congrArg (fun ys : List Read => ys.map Prod.fst) same).symm.trans tapeEq
  have noTop : ¬ ∃ rd ∈ xs, rd.1.1 ≠ 0 ∧ rd.1.2.rank = top ∧
      ActualMixedRowLeadingAnnotations.NonlinearOperand rd.1.2 := by
    rintro ⟨rd,here,active⟩
    exact inactive ⟨rd.1,List.mem_map.mpr ⟨rd,here,rfl⟩,active⟩
  let ops := table top xs
  let row := exitRow top constant xs
  have source := exactCertifiedLinearExit f ρ top constant rs xs bounded tape noTop
  have calibrated := exactSyntaxOfLinearExit top constant xs
  have opsEq : (canonicalPacket top constant (rs.map Prod.fst) test positive).1 = ops := by
    change termsTable top (groupTyped (rs.map Prod.fst)) = ops
    rw [← terms]
    exact calibrated.2.1
  have formulaEq : (canonicalPacket top constant (rs.map Prod.fst) test positive).2 = choosePolarity (testFormula test row) positive := by
    change choosePolarity (testFormula test (termsRow top constant (groupTyped (rs.map Prod.fst)))) positive = _
    rw [← terms,calibrated.2.2]
  dsimp only
  rw [opsEq,formulaEq]
  have rowPlain : PlainPreparedRow row := source.1.1 _ List.mem_cons_self
  have rowScope : ∀ name ∈ NormalForm.rowVariables row, name ≤ ops.length := source.1.2
  obtain ⟨someSlots,_,fit⟩ := source.2.1
  refine ⟨safePolarity ops _ (safeTest ops test row rowPlain rowScope) positive,⟨someSlots,fit⟩,?_⟩
  intro ν tied
  have result := source.2.2 ν tied
  refine ⟨result.1,result.2.1,?_,?_⟩
  · have bits := boolMeaning test row (Function.update ν 0 (ρ top)) adm positive
    rw [result.2.2.2] at bits
    exact bits
  · intro z
    obtain ⟨_,liveZ,val⟩ := result.2.2.1 z
    have bits := boolMeaning test row (Function.update ν 0 z) adm positive
    rw [val] at bits
    exact ⟨liveZ,bits⟩

end LogicLineages.PermittedControl.ActualCanonicalTerminalTruth
