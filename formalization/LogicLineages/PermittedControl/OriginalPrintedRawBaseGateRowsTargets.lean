module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadTargets
public import LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrixTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRows
open OrdinalComparison
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalPrintedCircuitNumericRead (RawGate encodeGate)
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedCode)
open NaturalAffineGateGraph (Expression)
open OriginalNormalizedCircuitMatrix (affineRows limitRows rowsList)

abbrev AffineArgs := Expression × Nat
abbrev LimitArgs := Nat × Expression × Nat × Nat
abbrev CollapseArgs := Nat × Nat × Nat × Nat
abbrev StepArgs := Nat × RawGate
abbrev BaseGate := OriginalMixedGateSequential.Gate

def coordinateCode (n : Nat) : LowerOperandCode := (0,n,(0,0,0,0))

def weightedCoord (t : Int × Nat) : WeightedCode := (t.1,coordinateCode t.2)

def affineEqualityCode (p : AffineArgs) : RawRow :=
  ((0,0),p.1.1,(-1,coordinateCode p.2) :: p.1.2.map weightedCoord)

def normGuardCode (head slot : Nat) : RawRow :=
  ((1,0),-(rawNormCode head : Int),[(1,coordinateCode slot)])

def zeroCode : Nat := rawNoteEncode AffineCollapseGuardRows.zeroTarget.1

def collapseEqualityCode (head slot output : Nat) : RawRow :=
  ((0,0),0,[(-1,coordinateCode output),
    (1,(1,slot,(1,0,head,zeroCode))),
    (1,(2,slot,(1,0,head,zeroCode)))])

def limitRowsCode (p : LimitArgs) : List RawRow :=
  [affineEqualityCode (p.2.1,p.2.2.1), normGuardCode p.1 p.2.2.1,
    collapseEqualityCode p.1 p.2.2.1 p.2.2.2]

/-- One original collapse with a supplied candidate hidden coordinate.
The infinite branch uses the original split head and finite tail.
Calibration is only for the genuine typed source encoding. -/
def collapseRowsCode (p : CollapseArgs) : List RawRow :=
  let head := p.1
  let source := p.2.1
  let slot := p.2.2.1
  let output := p.2.2.2
  if encodedFiniteTest head then
    [affineEqualityCode (((encodedFiniteValue head : Int),[(1,source)]),output)]
  else
    let split := (rawSplitCode head).unpair
    limitRowsCode (split.1,((rawNormCode split.1 + split.2 : Nat),[(1,source)]),slot,output)

/-- Exactly one original affine or fixed-head base gate. Both finite and
infinite collapse occurrences advance the candidate; the finite branch
emits no row for it. Other tags are outside this assembler. -/
def stepCode (p : StepArgs) : Option (Nat × List RawRow) :=
  let v := p.2
  let out := v.2.2.1
  if v.1 = 0 then some (p.1,[affineEqualityCode (v.2.2.2.2,out)])
  else if v.1 = 1 then
    some (p.1+1,collapseRowsCode (v.2.2.2.1.1,v.2.1,p.1,out))
  else none

def nextSlot (n : Nat) : BaseGate → Nat
  | .affine .. => n
  | .collapse _ => n+1

def ExactBaseRawAffine : Prop :=
  ∀ e : Expression, ∀ output : Nat,
    [affineEqualityCode (e,output)] = (affineRows e output).map encodeRow

def ExactBaseRawNormLimit : Prop :=
  ∀ (head : Nat) (e : Expression) (input output : Nat),
    OriginalNormalizedCircuitMatrix.LimitHead head →
      limitRowsCode (head,e,input,output) = (limitRows head e input output).map encodeRow

def ExactOriginalRawBaseGateStep : Prop :=
  ∀ (g : BaseGate) (n : Nat),
    stepCode (n,encodeGate (.base g)) =
      some (nextSlot n g,
        (rowsList (OriginalPrintedCircuitNormalization.normalizeFrom n [.base g])).map encodeRow)

def ExactOriginalRawBaseGateEffectivity : Prop :=
  Primrec affineEqualityCode ∧ Primrec limitRowsCode ∧ Primrec collapseRowsCode ∧ Primrec stepCode

def FullOriginalPrintedRawBaseGateRows : Prop :=
  ExactBaseRawAffine ∧ ExactBaseRawNormLimit ∧ ExactOriginalRawBaseGateStep ∧
    ExactOriginalRawBaseGateEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawBaseGateRows
