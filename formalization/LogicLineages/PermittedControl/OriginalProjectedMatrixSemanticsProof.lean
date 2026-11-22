module
public import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsTargets
import LogicLineages.PermittedControl.OriginalProjectedMatrixDecodeProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsAvailabilityProof
import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsSignedReadProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixProof
import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixSnapshotProof
import LogicLineages.PermittedControl.AffineCollapsePairListLowPrefixProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand PreparedTableTied)
open OriginalProjectedMatrixDecode (LiteralRow exactProjectedMatrixDecode)
open OriginalPlainTerminalMatrix (rows snapshot atomAnswer exactPlainTerminalSuffix exactPlainTerminalSnapshot)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)

private theorem exactValues (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (fit : PreparedTableTied f top ρ ops ν) {atoms : List NormalForm.Atom} {rs : List Row}
    (literal : List.Forall₂ (LiteralRow ops) atoms rs) (values : Snapshot) :
    actualRows f ρ rs values ↔ values = atoms.map (fun a => (NormalForm.rowValue a.row ν,atomAnswer ν a)) := by
  induction literal generalizing values with
  | nil => cases values <;> simp [actualRows]
  | @cons a r atoms rs head tail ih =>
      cases values with
      | nil => simp [actualRows]
      | cons pair values =>
          rcases pair with ⟨v,b⟩
          have cell := literalSnapshot f ρ top ops ν fit a r head v b
          constructor
          · rintro ⟨adm,measured,bit,rest⟩
            exact congrArg₂ List.cons (cell.mp ⟨adm,measured,bit⟩) ((ih values).mp rest)
          · intro same
            obtain ⟨h₁,h₂⟩ := List.cons.inj same
            obtain ⟨adm,measured,bit⟩ := cell.mpr h₁
            exact ⟨adm,measured,bit,(ih values).mpr h₂⟩

theorem exactDecodedRowSnapshots : ExactDecodedRowSnapshots := by
  intro f ρ top ops ν fit p rs decoded values
  exact exactValues f ρ top ops ν fit ((exactProjectedMatrixDecode.2.1 ops p rs).mp decoded) values

theorem exactDecodedSuffix : ExactDecodedSuffix := by
  intro f ρ top ops ν fit p plain rs decode positive
  have old := exactPlainTerminalSuffix f ν p plain positive
  have choose (snap : Snapshot) := (exactDecodedRowSnapshots f ρ top ops ν fit p rs decode snap).trans
    (exactPlainTerminalSnapshot f ν p plain snap).symm
  constructor
  · intro h
    obtain ⟨values,source,accepted⟩ := old.mp h
    exact ⟨values,(choose values).mpr source,accepted⟩
  · rintro ⟨values,actual,accepted⟩
    exact old.mpr ⟨values,(choose values).mp actual,accepted⟩

theorem exactResidualMatrixInterface : ExactResidualMatrixInterface := by
  intro f ρ top ops ν p rs pays plain decoded positive
  have guardsExact := exactAvailabilityRows.2.1 f ρ ops
  constructor
  · rintro ⟨live,terminal⟩
    obtain ⟨guards,measured,yes⟩ := guardsExact.mp live
    have len : guards.length = ops.length := by
      simpa only [availabilityRows,List.length_map] using actualLength f ρ (availabilityRows ops) guards measured
    obtain ⟨vals,rowsRead,accepted⟩ :=
      (exactDecodedSuffix f ρ top ops ν (pays live) p plain rs decoded positive).mp terminal
    have append := AffineCollapsePairListLow.actualRowsAppend f ρ (availabilityRows ops) rs guards vals
      (by simpa only [availabilityRows,List.length_map] using len.symm)
    exact ⟨guards,vals,len,yes,append.mpr ⟨measured,rowsRead⟩,accepted⟩
  · rintro ⟨guards,vals,len,yes,source,accepted⟩
    have split := AffineCollapsePairListLow.actualRowsAppend f ρ (availabilityRows ops) rs guards vals
      (by simpa only [availabilityRows,List.length_map] using len.symm)
    obtain ⟨actualGuards,actualRows⟩ := split.mp source
    have live := guardsExact.mpr ⟨guards,actualGuards,yes⟩
    exact ⟨live,(exactDecodedSuffix f ρ top ops ν (pays live) p plain rs decoded positive).mpr
      ⟨vals,actualRows,accepted⟩⟩

end LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
