module
public import LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRowsTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRowsTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawGraphAllocatorTargets
public import LogicLineages.PermittedControl.OriginalPrintedPlainMatrixInfiniteLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawGraphRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate)
open OriginalPrintedCircuitNormalization (normalizeFrom)
open OriginalNormalizedCircuitMatrix (rowsList)
open OriginalPrintedRawGraphAllocator (OriginalArgs ExactOriginalRawGraphAllocator initialCode)
open OriginalPrintedRawBaseGateRows (StepArgs)

abbrev State := Nat × List RawRow
abbrev FoldArgs := List RawGate × Option State

def onGate (p : StepArgs) : Option State :=
  if p.2.1 ≤ 1 then OriginalPrintedRawBaseGateRows.stepCode p
  else OriginalPrintedRawFieldGateRows.stepCode p

def appendEmission (prior : List RawRow) (out : State) : State :=
  (out.1,prior ++ out.2)

def advancePresent (s : State) (g : RawGate) : Option State :=
  (onGate (s.1,g)).map (appendEmission s.2)

def advance (s : Option State) (g : RawGate) : Option State :=
  s.bind (fun st => advancePresent st g)

def run (gs : List RawGate) (s : Option State) : Option State :=
  gs.foldl advance s

def rowsCode (p : OriginalArgs) : Option (List RawRow) :=
  (run p.2.2 (some (initialCode p,[]))).map Prod.snd

def nextSlot (n : Nat) : Gate → Nat
  | .base g => OriginalPrintedRawBaseGateRows.nextSlot n g
  | .field _ => n

def finalSlot (n : Nat) (gs : List Gate) : Nat :=
  gs.foldl nextSlot n

def ExactOriginalRawGraphGate : Prop :=
  ∀ (g : Gate) (n : Nat), onGate (n,encodeGate g) =
    some (nextSlot n g,(rowsList (normalizeFrom n [g])).map encodeRow)

def ExactOriginalRawGraphRun : Prop :=
  (∀ gs : List RawGate, run gs none = none) ∧
  ∀ (gs : List Gate) (n : Nat) (prior : List RawRow),
    run (gs.map encodeGate) (some (n,prior)) =
      some (finalSlot n gs,prior ++ (rowsList (normalizeFrom n gs)).map encodeRow)

def ExactOriginalRawGraphRows : Prop :=
  ExactOriginalRawGraphAllocator →
  ∀ (known : List Nat) (p : NormalForm.Formula) (gs : List Gate),
    rowsCode (known,p.encode,gs.map encodeGate) =
      some ((rowsList (OriginalPrintedPlainMatrixInfiniteLow.circuit known gs p)).map encodeRow)

def ExactOriginalRawGraphRowsEffectivity : Prop :=
  Primrec onGate ∧ Primrec₂ advance ∧ Primrec₂ run ∧
  (Primrec initialCode → Primrec rowsCode)

def FullOriginalPrintedRawGraphRows : Prop :=
  ExactOriginalRawGraphGate ∧ ExactOriginalRawGraphRun ∧ ExactOriginalRawGraphRows ∧
    ExactOriginalRawGraphRowsEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawGraphRows
