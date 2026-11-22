module
public import LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate)
open PreparedProjection (LowerOperandCode)
open OriginalPrintedRawBaseGateRows (coordinateCode normGuardCode StepArgs)
open OriginalNaturalFieldGates (Gate)

def equalityCode (operand : LowerOperandCode) (output : Nat) : RawRow :=
  ((0,0),0,[(-1,coordinateCode output),(1,operand)])

def zeroCode (output : Nat) : RawRow :=
  ((0,0),0,[(-1,coordinateCode output)])

def identityShapeCode (head : Nat) : RawRow :=
  ((0,0),if terminalScanGuard (head,head) then 0 else 1,[])

def identityRowsCode (count : Bool) (head source output : Nat) : List RawRow :=
  [identityShapeCode head,normGuardCode head source,
    if count then zeroCode output else equalityCode (coordinateCode source) output]

/-- Exact raw field-gate row transcription on genuine typed source codes.
The identity convention emits its actual explicit shape and norm rows,
not a failed proper read or an omitted domain condition. -/
def rowsCode (p : RawGate) : Option (List RawRow) :=
  let tag := p.1
  let source := p.2.1
  let output := p.2.2.1
  let head := p.2.2.2.1.1
  let target := p.2.2.2.1.2
  if tag = 2 then some [equalityCode (1,source,(0,head,0,0)) output]
  else if tag = 3 then some [equalityCode (1,source,(1,0,head,target)) output]
  else if tag = 4 then some [equalityCode (2,source,(1,0,head,target)) output]
  else if tag = 5 then some (identityRowsCode false head source output)
  else if tag = 6 then some (identityRowsCode true head source output)
  else none

def stepCode (p : StepArgs) : Option (Nat × List RawRow) :=
  (rowsCode p.2).map (fun rows => (p.1,rows))

def ExactOriginalRawFieldGateRows : Prop :=
  ∀ g : Gate, rowsCode (encodeGate (.field g)) = some ((OriginalFieldGateMatrix.rows g).map encodeRow)

def ExactOriginalRawFieldGateStep : Prop :=
  ∀ (g : Gate) (n : Nat),
    stepCode (n,encodeGate (.field g)) =
      some (n,(OriginalNormalizedCircuitMatrix.rowsList
        (OriginalPrintedCircuitNormalization.normalizeFrom n [.field g])).map encodeRow)

def ExactOriginalRawFieldGateEffectivity : Prop :=
  Primrec rowsCode ∧ Primrec stepCode

def FullOriginalPrintedRawFieldGateRows : Prop :=
  ExactOriginalRawFieldGateRows ∧ ExactOriginalRawFieldGateStep ∧ ExactOriginalRawFieldGateEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
