module
public import LogicLineages.PermittedControl.StageCallbackRawLevelTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open RawPacketAlgebra (encodePacket)
open StageCallbackRawLevel (orderCode)
open MixedSameRankResidue (WeightedCode)
open ActualCanonicalOperandGrouping (groupRaw)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualRawSignedStaticCeiling (RawSyntax encodeSyntax)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)

/-- Terms of rank strictly below `top`, in literal order. The rank is the
second component of the operand code. -/
def lowerCode (top : Nat) (ts : List WeightedCode) : List WeightedCode :=
  ts.foldr (fun t rest => if t.2.2.1 < top then t :: rest else rest) []

/-- Total signed weight at rank `top`. -/
def slopeCode (top : Nat) (ts : List WeightedCode) : Int :=
  ts.foldr (fun t acc => if t.2.2.1 = top then t.1 + acc else acc) 0

/-- One plain-variable item per term, named `i`, `i+1`, … in list order. -/
def namesCode (i : Nat) (ts : List WeightedCode) : List (Int × NormalForm.Code.ItemData) :=
  (ts.foldl (fun st t => (st.1+1,st.2 ++ [(t.1,((0 : Nat),st.1,(0 : Int),(0 : Int)))]))
    (i,([] : List (Int × NormalForm.Code.ItemData)))).2

/-- Row data of the linear exit: the constant, the greatest coordinate
(name zero) with its slope, then the lower table slots from name one. -/
def rowCode (top : Nat) (c : Int) (ts : List WeightedCode) : NormalForm.Code.RowData :=
  (c,(slopeCode top ts,((0 : Nat),(0 : Nat),(0 : Int),(0 : Int))) :: namesCode 1 (lowerCode top ts))

def atomCode (r : NormalForm.Code.RowData) : Nat :=
  6 * Encodable.encode (((0 : Nat),(0 : Nat),r) : NormalForm.Code.AtomData) + 2

/-- Formula code of an order test on a row: tag 0 equality (two
inequalities), tag 1 nonnegativity, any other tag strict positivity. -/
def testCode (order : Nat) (r : NormalForm.Code.RowData) : Nat :=
  if order = 0 then
    LinearRows.Code.conjunction (atomCode r) (atomCode (LinearRows.Code.rowScale (-1) r))
  else if order = 1 then atomCode r
  else atomCode (r.1 - 1,r.2)

def polarityCode (code : Nat) (positive : Bool) : Nat :=
  bif positive then code else 6 * code + 3

/-- Raw linear exit on ungrouped raw syntax: group, keep the lower table,
render the one row under the requested test and polarity. -/
def linearCode (top : Nat) (s : RawSyntax) (order : Nat) (positive : Bool) : PreparedPacketCode :=
  (Encodable.encode ((lowerCode top (groupRaw s.2)).map Prod.snd),
    polarityCode (testCode order (rowCode top s.1 (groupRaw s.2))) positive)

/-- The `linear` field of `Rendering.Exact`, for this program. -/
def ExactLinearCode : Prop :=
  ∀ (top : Nat) (s : SyntaxState) (test : OrderTest) (positive : Bool),
    linearCode top (encodeSyntax s) (orderCode test) positive =
      encodePacket (canonicalPacket top s.constant s.terms test.test positive)

def LinearCodeEffectivity : Prop :=
  Primrec₂ lowerCode ∧ Primrec₂ slopeCode ∧ Primrec₂ namesCode ∧
  Primrec (fun p : Nat × Int × List WeightedCode => rowCode p.1 p.2.1 p.2.2) ∧
  Primrec₂ testCode ∧
  Primrec (fun p : Nat × RawSyntax × Nat × Bool => linearCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def FullStageCallbackRenderLinear : Prop := ExactLinearCode ∧ LinearCodeEffectivity

end LogicLineages.PermittedControl.StageCallbackRender
