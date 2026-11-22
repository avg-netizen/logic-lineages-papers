module
public import LogicLineages.PermittedControl.RawPacketAlgebraGuardTargets
public import LogicLineages.PermittedControl.ActualGreatestRouteResidualTargets

@[expose] public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode)
open MixedSameRankResidue (WeightedCode)
open HeterogeneousSignedMatrixSlice (TestCode RawRow encodeRow)
open ActualPreparedSlotAppend (Packet)
open OriginalProjectedMatrixDecode (decode)
open ActualGreatestRouteResidual (Residual keep decodeRoute lowerFamily)

abbrev TermData := Int × NormalForm.Code.ItemData

/-- Code of `decodeTerm`: only a plain variable with positive name `j+1`
reads table slot `j`; name zero and the phi kinds give `none`. -/
def decodeTermCode (ops : List LowerOperandCode) (t : TermData) : Option WeightedCode :=
  cond (decide (t.2.1 = 0) && !decide (t.2.2.1 = 0))
    ((ops[t.2.2.1 - 1]?).map (fun op => (t.1,op))) none

def decodeTermsCode (ops : List LowerOperandCode) (ts : List TermData) : Option (List WeightedCode) :=
  ts.foldr (fun t acc => (decodeTermCode ops t).bind (fun x => acc.map (List.cons x))) (some [])

def testOfCode (a : NormalForm.Code.AtomData) : TestCode := if a.1 = 0 then (1,0) else (3,a.2.1+1)

def decodeRowCode (ops : List LowerOperandCode) (a : NormalForm.Code.AtomData) : Option RawRow :=
  (decodeTermsCode ops a.2.2.2).map (fun ts => (testOfCode a,a.2.2.1,ts))

def decodeAtomCode (ops : List LowerOperandCode) (payload : Nat) : Option RawRow :=
  decodeRowCode ops (LinearRows.Code.decodeAtom payload)

def decodeAtomsCode (ops : List LowerOperandCode) (payloads : List Nat) : Option (List RawRow) :=
  payloads.foldr (fun a acc => (decodeAtomCode ops a).bind (fun r => acc.map (List.cons r))) (some [])

/-- Code of `OriginalProjectedMatrixDecode.decode`, on the atom list of the formula code. -/
def decodeCode (ops : List LowerOperandCode) (code : Nat) : Option (List RawRow) :=
  decodeAtomsCode ops (LinearRows.Code.atoms code)

/-- NEW (minimal, composite) code for `Residual`: the tuple of the existing
codes of its three fields. No new code for any field. -/
abbrev ResidualCode := List LowerOperandCode × Nat × List RawRow

def encodeResidual (r : Residual) : ResidualCode :=
  (r.ops.map LowerOperand.code,r.formula.encode,r.atoms.map encodeRow)

def residualOf (o : PreparedPacketCode) : Option ResidualCode :=
  (decodeCode (tableOf o.1) o.2).map (fun rs => (tableOf o.1,o.2,rs))

def decodeRouteCode (minimum : Nat) (c : PreparedPacketCode) : Option ResidualCode :=
  residualOf (projectCode minimum c)

/-- Code of `keep`: the rank is the second component of every operand code. -/
def keepCode (top : Nat) (cs : List PreparedPacketCode) : List PreparedPacketCode :=
  cs.filter (fun c => (tableOf c.1).all (fun op => decide (op.2.1 < top)))

def lowerFamilyCode (top minimum : Nat) (cs : List PreparedPacketCode) : List ResidualCode :=
  (keepCode top cs).filterMap (decodeRouteCode minimum)

def ExactDecodeCode : Prop :=
  ∀ (ops : List LowerOperand) (p : NormalForm.Formula),
    decodeCode (ops.map LowerOperand.code) p.encode = (decode ops p).map (List.map encodeRow)

def ExactDecodeRouteCode : Prop :=
  ∀ (minimum : Nat) (q : Packet),
    decodeRouteCode minimum (encodePacket q) = (decodeRoute minimum q).map encodeResidual

def ExactKeepCode : Prop :=
  ∀ (top : Nat) (qs : List Packet), keepCode top (qs.map encodePacket) = (keep top qs).map encodePacket

def ExactLowerFamilyCode : Prop :=
  ∀ (top minimum : Nat) (qs : List Packet),
    lowerFamilyCode top minimum (qs.map encodePacket) = (lowerFamily top minimum qs).map encodeResidual

def ResidualCalibration : Prop :=
  ExactDecodeCode ∧ ExactDecodeRouteCode ∧ ExactKeepCode ∧ ExactLowerFamilyCode

def ResidualEffectivity : Prop :=
  Primrec₂ decodeCode ∧ Primrec₂ decodeRouteCode ∧ Primrec₂ keepCode ∧
    Primrec (fun x : Nat × Nat × List PreparedPacketCode => lowerFamilyCode x.1 x.2.1 x.2.2)

def FullRawPacketAlgebraResidual : Prop := ResidualCalibration ∧ ResidualEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
