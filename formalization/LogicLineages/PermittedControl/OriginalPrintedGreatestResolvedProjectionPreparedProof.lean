module
public import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjectionTransportProof
import LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedMatrixRankProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionSyntaxProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionPrefixProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixSnapshotProof
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedGreatestResolvedMatrix (prefixRows fullRows PacketAccepts exactResolvedMatrixTopLinear)
open OriginalPrintedPlainMatrixLinearProjection (top replay conjoin atomMap lowerBound lowerSafe
  lowerMeaning conjoinSafe atomMapSafe atomMapMeaning truePrefix admitsAtom)
open ActualFiniteOrderBranches (rename realized)
open OriginalMatrixDenseRanks (renameRow)
open OriginalMatrixLinearRowFormula (rowFormula choosePolarity exactLinearRowFormula
  safeAnd safePolarity safeFalsity)
open OriginalPlainTerminalMatrix (atomRow atomAnswer snapshot exactPlainTerminalSnapshot exactPlainTerminalSuffix)
open HeterogeneousSignedMatrixSlice (Row actualRows)
open PreparedProjection (PreparedInput)
open SignedRowGuardedTest (Test)

private theorem admittedExact (test : Test) : admittedCode test = true ↔ test.Admitted := by
  cases test with
  | equalZero => simp [admittedCode,Test.Admitted]
  | nonnegative => simp [admittedCode,Test.Admitted]
  | positive => simp [admittedCode,Test.Admitted]
  | congruence m => simp [admittedCode,Test.Admitted]

theorem exactResolvedPrepared : ExactResolvedPrepared := by
  intro f θ known gates p plain branch member checked minimum positive
  let pre := prefixRows known gates p branch
  let rs := ranked known gates p branch
  let ρ := realized θ branch
  let ops := table known gates p branch
  let compile := emit branch ops
  have linear := (exactResolvedMatrixTopLinear θ known gates p branch member checked).2
  have hPre (r : Row) (hr : r ∈ pre) : r ∈ fullRows known gates p branch :=
    List.mem_append_left _ hr
  have hAtom (a : NormalForm.Atom) (ha : a ∈ LinearRows.atoms p) :
      atomRow a ∈ fullRows known gates p branch :=
    List.mem_append_right _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hRow (r : Row) (hr : r ∈ fullRows known gates p branch) :=
    exactLinearRowFormula f ρ (top branch) rs linear (renameRow (rename branch) r)
      (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have prepared (r : Row) (hr : r ∈ fullRows known gates p branch) : PreparedInput ops (compile r) := by
    by_cases h : admittedCode r.1 = true
    · simpa only [compile,emit,if_pos h,ops,table,rs] using (hRow r hr).1
    · simpa only [compile,emit,if_neg h] using safeFalsity ops
  have prefixShape : PreparedInput ops (conjoin (pre.map compile)) := by
    apply conjoinSafe
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact prepared r (hPre r hr)
  have suffixShape : PreparedInput ops (atomMap (fun a => compile (atomRow a)) p) :=
    atomMapSafe ops _ p (fun a ha => prepared (atomRow a) (hAtom a ha))
  refine ⟨safeAnd ops _ _ (lowerSafe ops minimum)
    (safeAnd ops _ _ prefixShape (safePolarity ops _ suffixShape positive)),?_⟩
  intro ν fit z
  let output := replay θ known gates p branch z
  let slots := Function.update ν 0 z
  have meaning (r : Row) (hr : r ∈ fullRows known gates p branch) :
      (compile r).eval slots ↔ ∃ v : Int, actualRows f output [r] [(v,true)] := by
    by_cases h : admittedCode r.1 = true
    · have legal : r.1.Admitted := (admittedExact r.1).mp h
      have row := (hRow r hr).2 legal ν fit z true
      have transported := row.trans (exists_congr fun v =>
        transport θ known gates p branch member checked z [r]
          (fun q hq => (List.mem_singleton.mp hq).symm ▸ hr) f [(v,true)])
      simpa only [compile,emit,if_pos h,choosePolarity,if_true,ops,table,rs,slots,output] using transported
    · have illegal : ¬ r.1.Admitted := fun yes => h ((admittedExact r.1).mpr yes)
      change (if admittedCode r.1 then _ else NormalForm.Formula.falsity).eval slots ↔ _
      rw [if_neg h]
      exact ⟨False.elim,fun ⟨_,live⟩ => illegal live.1⟩
  have graphCheck := truePrefix f output slots pre compile (fun r hr => meaning r (hPre r hr))
  have suffixAtom (a : NormalForm.Atom) (ha : a ∈ LinearRows.atoms p) :
      (compile (atomRow a)).eval slots ↔ a.eval output := by
    have onePlain : PreparedProjection.PlainPreparedFormula (.atom a) := by
      intro b hb
      have same : b = a := List.mem_singleton.mp hb
      subst b
      exact plain a ha
    have per := meaning (atomRow a) (hAtom a ha)
    constructor
    · intro success
      obtain ⟨v,live⟩ := per.mp success
      exact (exactPlainTerminalSuffix f output (.atom a) onePlain true).mpr ⟨[(v,true)],live,rfl⟩
    · intro holds
      have bit := (OriginalMixedTerminalTest.exactTerminalTestRead (.rows (.atom a)) onePlain output true).mpr holds
      have atomBit : atomAnswer output a = true := by cases a <;> exact bit
      have actual := (exactPlainTerminalSnapshot f output (.atom a) onePlain (snapshot output (.atom a))).mpr rfl
      change actualRows f output [atomRow a] [(NormalForm.rowValue a.row output,atomAnswer output a)] at actual
      rw [atomBit] at actual
      exact per.mpr ⟨_,actual⟩
  have suffix : (choosePolarity (atomMap (fun a => compile (atomRow a)) p) positive).eval slots ↔
      (OriginalMixedTerminalTest.Test.rows p).atPolarity positive output := by
    have compiled := atomMapMeaning (fun a => compile (atomRow a)) p slots output suffixAtom
    cases positive with
    | true => exact compiled
    | false => exact not_congr compiled
  have hz : (lowerBound minimum).eval slots ↔ minimum ≤ z := by
    simpa only [slots,Function.update_self] using lowerMeaning minimum slots
  exact and_congr hz (and_congr graphCheck
    (suffix.trans (exactPlainTerminalSuffix f output p plain positive)))

end LogicLineages.PermittedControl.OriginalPrintedGreatestResolvedProjection
