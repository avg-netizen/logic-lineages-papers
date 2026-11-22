module
public import LogicLineages.PermittedControl.StageCallbackRawLevelTargets
public import LogicLineages.PermittedControl.RawFieldComparisonFormTargets
public import LogicLineages.PermittedControl.HighFieldComparisonTargets
public import LogicLineages.PermittedControl.HighFieldPreparedPacketTargets
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackGuardRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open FieldComparison (LongFieldCode)
open RawPacketAlgebra (encodePacket tableOf appendCode unitCode)
open MixedSameRankResidue (WeightedOperand)
open ActualRawComparisonCeiling (LabelCode PairCode encodeLabel encodePair orderedPairs)
open ActualFullValueLabels (Label labels)
open ActualFullLabelPairGuards (Pair Answer lowerFormula)
open ActualFiniteFullValueGuards (pairs compile)

/-- Operand code of the bare raw coordinate `rank`. -/
def slotCode (rank : Nat) : LowerOperandCode :=
  ((0 : Nat),rank,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat)))

/-- Literal code of `StableSortedHighField.orderGuard n`: the row `-1 + x₀ - xₙ ≥ 0`. -/
def orderGuardCode (n : Nat) : Nat :=
  6 * Encodable.encode (((0 : Nat),(0 : Nat),((-1 : Int),
    [((1 : Int),((0 : Nat),(0 : Nat),(0 : Int),(0 : Int))),
     ((-1 : Int),((0 : Nat),n,(0 : Int),(0 : Int)))])) : NormalForm.Code.AtomData) + 2

/-- Append the bare lower coordinate slot and the strict-order guard to a base packet code. -/
def strictFromBase (lo : Nat) (b : PreparedPacketCode) : PreparedPacketCode :=
  (Encodable.encode (tableOf b.1 ++ [slotCode lo]),
    LinearRows.Code.conjunction (orderGuardCode ((tableOf b.1).length + 1)) b.2)

/-- Strict-order case: the accepted base packet compiler `HighFieldPreparedPacket.compile`. -/
def strictCode (F G : LongFieldCode) (lo hi wanted : Nat) : PreparedPacketCode :=
  strictFromBase lo (HighFieldPreparedPacket.compile (F,G,lo,hi,wanted))

/-- Code of `constantFormula 0 answer wanted`. -/
def constantCode (answer wanted : Nat) : Nat := if answer = wanted then 0 else 1

/-- Equal-rank case: the accepted raw short-field normalization and same-rank form. -/
def equalCode (F G : LongFieldCode) (wanted : Nat) : PreparedPacketCode :=
  (Encodable.encode ([] : List LowerOperandCode),
    constantCode (FieldComparison.rawSameForm (FieldComparison.normalizeHighFieldCode F)
      (FieldComparison.normalizeHighFieldCode G)) wanted)

/-- Code of `topPacket` on an answer code `wanted ∈ {0,1,2}`; the reversed
orientation asks for `2 - wanted`. -/
def topCode (F G : LongFieldCode) (i j wanted : Nat) : PreparedPacketCode :=
  if i < j then strictCode F G i j wanted
  else if j < i then strictCode G F j i (2 - wanted)
  else equalCode F G wanted

def lowerFormulaCode (a : Nat) : Nat :=
  if a = 0 then (lowerFormula .less).encode
  else if a = 1 then (lowerFormula .equal).encode
  else (lowerFormula .greater).encode

def lowerPairCode (p : PairCode) (a : Nat) : PreparedPacketCode :=
  (Encodable.encode ([((1 : Nat),p.1.1,p.1.2),((1 : Nat),p.2.1,p.2.2)] : List LowerOperandCode),
    lowerFormulaCode a)

/-- Code of `ActualFullLabelPairGuards.packet`. -/
def pairCode (top : Nat) (p : PairCode) (a : Nat) : PreparedPacketCode :=
  if max p.1.1 p.2.1 < top then lowerPairCode p a else topCode p.1.2 p.2.2 p.1.1 p.2.1 a

def falseCode : PreparedPacketCode := encodePacket ([],.falsity)

/-- Code of `ActualFiniteFullValueGuards.compile`, with the same treatment of
tapes of the wrong length. -/
def compileCode (top : Nat) : List PairCode → List Nat → PreparedPacketCode
  | [],[] => unitCode
  | p::ps,a::as => appendCode (pairCode top p a) (compileCode top ps as)
  | _,_ => falseCode

/-- The `guard` rendering. -/
def guardCode (top : Nat) (ls : List LabelCode) (as : List Nat) : PreparedPacketCode :=
  compileCode top (orderedPairs ls) as

def ExactPairCode : Prop :=
  ∀ (top : Nat) (p : Pair) (a : Answer),
    pairCode top (encodePair p) a.code = encodePacket (ActualFullLabelPairGuards.packet top p a)

def ExactCompileCode : Prop :=
  ∀ (top : Nat) (ps : List Pair) (as : List Answer),
    compileCode top (ps.map encodePair) (as.map Answer.code) = encodePacket (compile top ps as)

/-- The `guard` field of `Rendering.Exact`, for this program: every grouped
term list and every tape, of any length. -/
def ExactGuardCode : Prop :=
  ∀ (top : Nat) (grouped : List WeightedOperand) (a : List Answer),
    guardCode top ((labels grouped).map encodeLabel) (a.map Answer.code) =
      encodePacket (StageCallbackCanonicalRoutes.guard top grouped a)

def GuardCodeEffectivity : Prop :=
  Primrec (fun p : Nat × PairCode × Nat => pairCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List PairCode × List Nat => compileCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List LabelCode × List Nat => guardCode p.1 p.2.1 p.2.2)

def FullStageCallbackGuardRender : Prop :=
  ExactPairCode ∧ ExactCompileCode ∧ ExactGuardCode ∧ GuardCodeEffectivity

end LogicLineages.PermittedControl.StageCallbackGuardRender
