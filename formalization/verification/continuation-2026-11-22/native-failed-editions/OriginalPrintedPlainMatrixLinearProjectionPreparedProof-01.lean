module
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTargets
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionSyntaxProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionTransportProof
import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjectionPrefixProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaProof
import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixSnapshotProof
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalPrintedPlainMatrixOrderBranches (SourceAccepts renamed)
open OriginalPrintedCircuitNormalization (Holds)
open OriginalNormalizedCircuitMatrix (rowsList)
open ActualFiniteOrderBranches (rename realized)
open OriginalMatrixDenseRanks (renameRow)
open OriginalMatrixLinearRowFormula (rowFormula choosePolarity exactLinearRowFormula safeAnd safePolarity)
open OriginalNormalizedMatrixPositiveSnapshots (exactPositiveCircuitSnapshots)
open OriginalPlainTerminalMatrix (atomRow atomAnswer snapshot exactPlainTerminalSnapshot exactPlainTerminalSuffix)
open HeterogeneousSignedMatrixSlice (Row actualRows)
open PreparedProjection (PreparedInput)

theorem exactAlreadyLinearPreparedCircuit : ExactAlreadyLinearPreparedCircuit := by
  intro f θ known gates p plain branch member checked linear minimum positive
  let gs := circuit known gates p
  let rs := renamed known gates p branch
  let ρ := realized θ branch
  let ops := table known gates p branch
  let emit : Row → NormalForm.Formula := fun r =>
    rowFormula (top branch) ops (renameRow (rename branch) r)
  have hPrefix (r : Row) (hr : r ∈ rowsList gs) : r ∈ matrix known gates p :=
    List.mem_append_left _ hr
  have hAtom (a : NormalForm.Atom) (ha : a ∈ LinearRows.atoms p) : atomRow a ∈ matrix known gates p :=
    List.mem_append_right _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have hRow (r : Row) (hr : r ∈ matrix known gates p) :=
    exactLinearRowFormula f ρ (top branch) rs linear (renameRow (rename branch) r)
      (rowInRenamed known gates p branch r hr)
  have prefixShape : PreparedInput ops (conjoin ((rowsList gs).map emit)) := by
    apply conjoinSafe
    intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    exact (hRow r (hPrefix r hr)).1
  have suffShape : PreparedInput ops (atomMap (fun a => emit (atomRow a)) p) :=
    atomMapSafe ops _ p (fun a ha => (hRow (atomRow a) (hAtom a ha)).1)
  refine ⟨safeAnd ops _ _ (lowerSafe ops minimum)
    (safeAnd ops _ _ prefixShape (safePolarity ops _ suffShape positive)),?_⟩
  intro ν fit z
  let output := replay θ known gates p branch z
  let slots := Function.update ν 0 z
  have meaning (r : Row) (hr : r ∈ matrix known gates p) (admitted : r.1.Admitted) :
      (emit r).eval slots ↔ ∃ v : Int, actualRows f output [r] [(v,true)] := by
    have prepared := (hRow r hr).2 admitted ν fit z true
    refine prepared.trans (exists_congr fun v => ?_)
    exact transportPart θ known gates p branch member checked z [r]
      (fun q hq => (List.mem_singleton.mp hq).symm ▸ hr) f [(v,true)]
  have graphCheck : (conjoin ((rowsList gs).map emit)).eval slots ↔ Holds f output gs := by
    refine (truePrefix f output slots (rowsList gs) emit
      (fun r hr => meaning r (hPrefix r hr) (admitsPrefix gs r hr))).trans ?_
    constructor
    · rintro ⟨snap,h,pass⟩
      exact ((exactPositiveCircuitSnapshots f output gs snap).mp ⟨h,pass⟩).1
    · intro graph
      exact ⟨_,(exactPositiveCircuitSnapshots f output gs _).mpr ⟨graph,rfl⟩⟩
  have suffixAtom (a : NormalForm.Atom) (ha : a ∈ LinearRows.atoms p) :
      (emit (atomRow a)).eval slots ↔ a.eval output := by
    have onePlain : PreparedProjection.PlainPreparedFormula (.atom a) := by
      intro b hb
      have equal : b = a := List.mem_singleton.mp hb
      subst b
      exact plain a ha
    have per := meaning (atomRow a) (hAtom a ha) (admitsAtom a)
    constructor
    · intro success
      obtain ⟨v,live⟩ := per.mp success
      exact (exactPlainTerminalSuffix f output (.atom a) onePlain true).mpr ⟨[(v,true)],live,rfl⟩
    · intro holds
      have bit := (OriginalMixedTerminalTest.exactTerminalTestRead (.rows (.atom a)) onePlain output true).mpr holds
      change atomAnswer output a = true at bit
      have actual := (exactPlainTerminalSnapshot f output (.atom a) onePlain (snapshot output (.atom a))).mpr rfl
      change actualRows f output [atomRow a] [(NormalForm.rowValue a.row output,atomAnswer output a)] at actual
      rw [bit] at actual
      exact per.mpr ⟨_,actual⟩
  have suffix : (choosePolarity (atomMap (fun a => emit (atomRow a)) p) positive).eval slots ↔
      (OriginalMixedTerminalTest.Test.rows p).atPolarity positive output := by
    have compiled := atomMapMeaning (fun a => emit (atomRow a)) p slots output suffixAtom
    cases positive with
    | true => exact compiled
    | false => exact not_congr compiled
  have hz : (lowerBound minimum).eval slots ↔ minimum ≤ z := by
    simpa only [slots,Function.update_self] using lowerMeaning minimum slots
  exact and_congr hz (and_congr graphCheck suffix)

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
