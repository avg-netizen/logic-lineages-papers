module
public import LogicLineages.PermittedControl.RawPacketAlgebraResidualTargets
public import LogicLineages.PermittedControl.ActualGuardedResidualBitFamilyTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets

@[expose] public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode)
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalProjectedMatrixSemantics (availabilityRows)
open ActualLowerRankChartRows (lowerChart)
open ActualGreatestRouteResidual (Residual)
open ActualGuardedResidualBitFamily (reify reifyFamily)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily)
open OriginalPrintedRawClauseAssembly (clausesCode)

/-- Code of `availabilityRows`: one literal row `0 + 1·op ≥ 0` per operand code. -/
def availabilityCode (ops : List LowerOperandCode) : List RawRow :=
  ops.map (fun op => (((1 : Nat),(0 : Nat)),(0 : Int),[((1 : Int),op)]))

/-- Code of `lowerChart B top`: the funding rows, then the rising rows. -/
def lowerChartCode (B top : Nat) : List RawBitRow :=
  ((List.range top).map (fun i =>
      ((((1 : Nat),(0 : Nat)),-(B : Int),[((1 : Int),((0 : Nat),i,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat))))]),true))) ++
    ((List.range (top-1)).map (fun i =>
      ((((2 : Nat),(0 : Nat)),(0 : Int),
        [((1 : Int),((0 : Nat),i+1,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat)))),
         ((-1 : Int),((0 : Nat),i,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat))))]),true)))

/-- Code of `reify`, by the accepted raw clause assembly `clausesCode` (#1343). -/
def reifyCode (C top : Nat) (r : ResidualCode) : RawFamily :=
  (clausesCode (r.2.1,true,availabilityCode r.1,r.2.2)).map (fun row => lowerChartCode C top ++ row)

def reifyFamilyCode (C top : Nat) (rs : List ResidualCode) : RawFamily :=
  rs.flatMap (reifyCode C top)

def ExactAvailabilityCode : Prop :=
  ∀ ops : List LowerOperand,
    availabilityCode (ops.map LowerOperand.code) = (availabilityRows ops).map encodeRow

def ExactLowerChartCode : Prop :=
  ∀ B top : Nat, lowerChartCode B top = (lowerChart B top).map encodeBitRow

def ExactReifyCode : Prop :=
  ∀ (C top : Nat) (out : Residual), reifyCode C top (encodeResidual out) = encodeFamily (reify C top out)

def ExactReifyFamilyCode : Prop :=
  ∀ (C top : Nat) (outs : List Residual),
    reifyFamilyCode C top (outs.map encodeResidual) = encodeFamily (reifyFamily C top outs)

def ReifyCalibration : Prop :=
  ExactAvailabilityCode ∧ ExactLowerChartCode ∧ ExactReifyCode ∧ ExactReifyFamilyCode

def ReifyEffectivity : Prop :=
  Primrec availabilityCode ∧ Primrec₂ lowerChartCode ∧
    Primrec (fun x : Nat × Nat × ResidualCode => reifyCode x.1 x.2.1 x.2.2) ∧
    Primrec (fun x : Nat × Nat × List ResidualCode => reifyFamilyCode x.1 x.2.1 x.2.2)

def FullRawPacketAlgebraReify : Prop := ReifyCalibration ∧ ReifyEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
