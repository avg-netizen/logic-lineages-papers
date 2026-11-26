module
public import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalTargets
import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalCalibrationProof
import LogicLineages.PermittedControl.ActualLinearExitProof
import LogicLineages.PermittedControl.ActualWeightedReadNormalizationActualProof
import LogicLineages.PermittedControl.ActualRankedNormalizationSyntaxSkeletonProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsAlgebraProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSyntaxLinearTerminal
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PlainPreparedRow PreparedInput PreparedTableTied lowerOperandRead)
open ActualZeroClassReplacement (Read readSum liftedReads)
open ActualRankedNormalizationSyntax (normalizedTerms exactNormalizedTermSkeleton)
open ActualWeightedReadNormalization (exactNormalizedReads normalizeReads)
open ActualFiniteSignedNodeBranch (StaticActive)
open ActualLinearExit (lowerReads table exitRow OriginalSlots replay exactActualLinearExit)
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

theorem exactActualSyntaxLinearTerminal : ExactActualSyntaxLinearTerminal := by
  intro f ρ top constant raw rs original scope live inactive test positive adm
  obtain ⟨xs,ok,_,_,_,_,_⟩ := (exactNormalizedReads f ρ rs).2 live
  have terms : xs.map Prod.fst = normalizedTerms raw :=
    (exactNormalizedTermSkeleton.1 f ρ rs xs ok).trans (congrArg normalizedTerms original)
  have bounded (rd : Read) (here : rd ∈ rs) : rd.1.2.rank ≤ top := by
    apply scope rd.1
    rw [← original]
    exact List.mem_map.mpr ⟨rd,here,rfl⟩
  have noTop : ¬ ∃ rd ∈ xs, rd.1.1 ≠ 0 ∧ rd.1.2.rank = top ∧
      ActualMixedRowLeadingAnnotations.NonlinearOperand rd.1.2 := by
    rintro ⟨rd,here,active⟩
    apply inactive
    refine ⟨rd.1,?_,active⟩
    rw [← terms]
    exact List.mem_map.mpr ⟨rd,here,rfl⟩
  let ops := table top xs
  let row := exitRow top constant xs
  have source := exactActualLinearExit f ρ top constant rs xs live bounded ok noTop
  have calibrated := exactSyntaxOfLinearExit top constant xs
  have opsEq : (packet top constant raw test positive).1 = ops := by
    change termsTable top (normalizedTerms raw) = ops
    rw [← terms]
    exact calibrated.2.1
  have formulaEq : (packet top constant raw test positive).2 = choosePolarity (testFormula test row) positive := by
    change choosePolarity (testFormula test (termsRow top constant (normalizedTerms raw))) positive = _
    rw [← terms,calibrated.2.2]
  change ∃ ys, normalizeReads f ρ rs = some ys ∧ _
  refine ⟨xs,ok,?_⟩
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

end LogicLineages.PermittedControl.ActualSyntaxLinearTerminal
