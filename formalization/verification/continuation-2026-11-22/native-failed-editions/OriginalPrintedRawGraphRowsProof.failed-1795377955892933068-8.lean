module
public import LogicLineages.PermittedControl.OriginalPrintedRawGraphRowsTargets
import LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRowsProof
import LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRowsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawGraphRows
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate)
open OriginalPrintedCircuitNormalization (normalizeFrom normalized)
open OriginalNormalizedCircuitMatrix (rowsList)
open OriginalPrintedRawGraphAllocator (initialCode)

private theorem baseTag (b : OriginalMixedGateSequential.Gate) :
    (encodeGate (.base b)).1 ≤ 1 := by
  cases b <;> simp [encodeGate]

private theorem fieldTag (f : OriginalNaturalFieldGates.Gate) :
    ¬ (encodeGate (.field f)).1 ≤ 1 := by
  cases f with
  | iterate _ _ _ => simp [encodeGate]
  | entry int _ _ => cases int <;> simp [encodeGate]
  | count int _ _ => cases int <;> simp [encodeGate]

theorem exactOriginalRawGraphGate : ExactOriginalRawGraphGate := by
  intro g n
  cases g with
  | base b =>
    simpa only [onGate,baseTag,if_pos,nextSlot] using
      OriginalPrintedRawBaseGateRows.exactOriginalRawBaseGateStep b n
  | field f =>
    simpa only [onGate,fieldTag,if_neg,nextSlot] using
      OriginalPrintedRawFieldGateRows.exactOriginalRawFieldGateStep f n

private theorem normalizeCons (n : Nat) (g : Gate) (gs : List Gate) :
    normalizeFrom n (g :: gs) =
      normalizeFrom n [g] ++ normalizeFrom (nextSlot n g) gs := by
  cases g with
  | field _ => rfl
  | base b => cases b <;> rfl

private theorem encodedCons (n : Nat) (g : Gate) (gs : List Gate) :
    (rowsList (normalizeFrom n (g :: gs))).map encodeRow =
      (rowsList (normalizeFrom n [g])).map encodeRow ++
        (rowsList (normalizeFrom (nextSlot n g) gs)).map encodeRow := by
  rw [normalizeCons]
  simp only [rowsList,List.flatMap_append,List.map_append]

private theorem runNone (gs : List RawGate) : run gs none = none := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    change run gs none = none
    exact ih

private theorem runEncoded (gs : List Gate) (n : Nat) (prior : List RawRow) :
    run (gs.map encodeGate) (some (n,prior)) =
      some (finalSlot n gs,prior ++ (rowsList (normalizeFrom n gs)).map encodeRow) := by
  induction gs generalizing n prior with
  | nil => simp [run,finalSlot,normalizeFrom,rowsList]
  | cons g gs ih =>
    change run (gs.map encodeGate)
      ((onGate (n,encodeGate g)).map (appendEmission prior)) =
      some (finalSlot (nextSlot n g) gs,prior ++
        (rowsList (normalizeFrom n (g :: gs))).map encodeRow)
    rw [exactOriginalRawGraphGate g n]
    change run (gs.map encodeGate)
      (some (nextSlot n g,prior ++ (rowsList (normalizeFrom n [g])).map encodeRow)) = _
    rw [ih,encodedCons,List.append_assoc]

theorem exactOriginalRawGraphRun : ExactOriginalRawGraphRun := ⟨runNone,runEncoded⟩

theorem exactOriginalRawGraphRows : ExactOriginalRawGraphRows := by
  intro alloc known p gs
  unfold rowsCode
  rw [alloc.2.2.2 known p gs,runEncoded]
  simp only [Option.map_some,List.nil_append,OriginalPrintedPlainMatrixInfiniteLow.circuit,normalized]

end LogicLineages.PermittedControl.OriginalPrintedRawGraphRows
