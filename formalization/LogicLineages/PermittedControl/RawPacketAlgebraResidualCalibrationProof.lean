module
public import LogicLineages.PermittedControl.RawPacketAlgebraResidualTargets
import LogicLineages.PermittedControl.RawPacketAlgebraJoinCalibrationProof
import LogicLineages.PermittedControl.RawPacketAlgebraGuardProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandCode PreparedPacketCode preparedTableBytes)
open MixedSameRankResidue (WeightedCode WeightedOperand encodeWeighted)
open HeterogeneousSignedMatrixSlice (TestCode RawRow Row encodeRow)
open ActualPreparedSlotAppend (Packet)
open ActualSelectedSignedRouteProjection (project)
open OriginalProjectedMatrixDecode (decode decodeTerm decodeTerms decodeAtom decodeAtoms)
open ActualGreatestRouteResidual (Residual keep decodeRoute lowerFamily)

theorem termCodeEq (ops : List LowerOperand) (t : Int × NormalForm.Summand) :
    decodeTermCode (ops.map LowerOperand.code) (t.1,t.2.data) = (decodeTerm ops t).map encodeWeighted := by
  obtain ⟨c,s⟩ := t
  cases s with
  | «variable» i =>
    cases i with
    | zero => rfl
    | succ j =>
      change ((ops.map LowerOperand.code)[j+1-1]?).map (fun op => (c,op)) =
        ((ops[j]?).map (fun op => (c,op))).map encodeWeighted
      rw [Nat.add_sub_cancel,List.getElem?_map]
      cases ops[j]? <;> rfl
  | phi i e => rfl
  | hyperPhi i e h => rfl

theorem termsCodeEq (ops : List LowerOperand) : ∀ ts : List (Int × NormalForm.Summand),
    decodeTermsCode (ops.map LowerOperand.code) (ts.map (fun a => (a.1,a.2.data))) =
      (decodeTerms ops ts).map (List.map encodeWeighted)
  | [] => rfl
  | t :: ts => by
    change (decodeTermCode (ops.map LowerOperand.code) (t.1,t.2.data)).bind
        (fun x => (decodeTermsCode (ops.map LowerOperand.code)
          (ts.map (fun a => (a.1,a.2.data)))).map (List.cons x)) =
      (decodeTerms ops (t :: ts)).map (List.map encodeWeighted)
    rw [termCodeEq ops t,termsCodeEq ops ts]
    simp only [decodeTerms]
    cases decodeTerm ops t <;> cases decodeTerms ops ts <;> rfl

theorem atomCodeEq (ops : List LowerOperand) (a : NormalForm.Atom) :
    decodeAtomCode (ops.map LowerOperand.code) (Encodable.encode a.data) = (decodeAtom ops a).map encodeRow := by
  have dec : LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
    simp only [LinearRows.Code.decodeAtom,Encodable.encodek,Option.getD_some]
  change decodeRowCode (ops.map LowerOperand.code) (LinearRows.Code.decodeAtom (Encodable.encode a.data)) = _
  rw [dec]
  cases a with
  | nonnegative r =>
    change (decodeTermsCode (ops.map LowerOperand.code) (r.2.map (fun x => (x.1,x.2.data)))).map
        (fun ts => (((1 : Nat),(0 : Nat)),r.1,ts)) =
      ((decodeTerms ops r.2).map (fun ts => (SignedRowGuardedTest.Test.nonnegative,r.1,ts))).map encodeRow
    rw [termsCodeEq]
    cases decodeTerms ops r.2 <;> rfl
  | divisible m r =>
    change (decodeTermsCode (ops.map LowerOperand.code) (r.2.map (fun x => (x.1,x.2.data)))).map
        (fun ts => (((3 : Nat),m+1),r.1,ts)) =
      ((decodeTerms ops r.2).map
        (fun ts => (SignedRowGuardedTest.Test.congruence (m+1),r.1,ts))).map encodeRow
    rw [termsCodeEq]
    cases decodeTerms ops r.2 <;> rfl

private theorem atomsStep (codes : List LowerOperandCode) (x : Nat) (xs : List Nat) :
    decodeAtomsCode codes (x :: xs) =
      (decodeAtomCode codes x).bind (fun r => (decodeAtomsCode codes xs).map (List.cons r)) := by
  simp only [decodeAtomsCode,List.foldr_cons]

theorem atomsCodeEq (ops : List LowerOperand) : ∀ as : List NormalForm.Atom,
    decodeAtomsCode (ops.map LowerOperand.code) (as.map (fun a => Encodable.encode a.data)) =
      (decodeAtoms ops as).map (List.map encodeRow)
  | [] => rfl
  | a :: as => by
    rw [List.map_cons,atomsStep,atomCodeEq ops a,atomsCodeEq ops as]
    simp only [decodeAtoms]
    cases decodeAtom ops a <;> cases decodeAtoms ops as <;> rfl

theorem decodeCodeEq (ops : List LowerOperand) (p : NormalForm.Formula) :
    decodeCode (ops.map LowerOperand.code) p.encode = (decode ops p).map (List.map encodeRow) := by
  change decodeAtomsCode (ops.map LowerOperand.code) (LinearRows.Code.atoms p.encode) =
    (decodeAtoms ops (LinearRows.atoms p)).map (List.map encodeRow)
  rw [LinearRowsCodeProof.atoms_calibration]
  exact atomsCodeEq ops (LinearRows.atoms p)

theorem exactDecodeCode : ExactDecodeCode := decodeCodeEq

theorem decodeRouteCodeEq (minimum : Nat) (q : Packet) :
    decodeRouteCode minimum (encodePacket q) = (decodeRoute minimum q).map encodeResidual := by
  change residualOf (projectCode minimum (encodePacket q)) = _
  rw [projectCodeEq]
  change (decodeCode (tableOf (preparedTableBytes (project minimum q).1)) (project minimum q).2.encode).map
      (fun rs => (tableOf (preparedTableBytes (project minimum q).1),(project minimum q).2.encode,rs)) =
    ((decode (project minimum q).1 (project minimum q).2).map
      (fun rs => (⟨(project minimum q).1,(project minimum q).2,rs⟩ : Residual))).map encodeResidual
  rw [tableBytes,decodeCodeEq]
  cases decode (project minimum q).1 (project minimum q).2 <;> rfl

theorem exactDecodeRouteCode : ExactDecodeRouteCode := decodeRouteCodeEq

theorem rankCode (op : LowerOperand) : op.code.2.1 = op.rank := by
  cases op <;> rfl

theorem keepCodeEq (top : Nat) (qs : List Packet) :
    keepCode top (qs.map encodePacket) = (keep top qs).map encodePacket := by
  have same (q : Packet) :
      (tableOf (encodePacket q).1).all (fun op => decide (op.2.1 < top)) =
        q.1.all (fun op => decide (op.rank < top)) := by
    change (tableOf (preparedTableBytes q.1)).all _ = _
    rw [tableBytes]
    simp only [List.all_map,Function.comp_def,rankCode]
  change List.filter _ (qs.map encodePacket) = List.map encodePacket (List.filter _ qs)
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro q _
  exact same q

theorem exactKeepCode : ExactKeepCode := keepCodeEq

theorem filterMapCodeEq (minimum : Nat) : ∀ qs : List Packet,
    (qs.map encodePacket).filterMap (decodeRouteCode minimum) =
      (qs.filterMap (decodeRoute minimum)).map encodeResidual
  | [] => rfl
  | q :: qs => by
    rw [List.map_cons,List.filterMap_cons,List.filterMap_cons,decodeRouteCodeEq,filterMapCodeEq minimum qs]
    cases decodeRoute minimum q <;> rfl

theorem lowerFamilyCodeEq (top minimum : Nat) (qs : List Packet) :
    lowerFamilyCode top minimum (qs.map encodePacket) = (lowerFamily top minimum qs).map encodeResidual := by
  change (keepCode top (qs.map encodePacket)).filterMap (decodeRouteCode minimum) =
    ((keep top qs).filterMap (decodeRoute minimum)).map encodeResidual
  rw [keepCodeEq]
  exact filterMapCodeEq minimum (keep top qs)

theorem exactLowerFamilyCode : ExactLowerFamilyCode := lowerFamilyCodeEq

theorem residualCalibration : ResidualCalibration :=
  ⟨exactDecodeCode,exactDecodeRouteCode,exactKeepCode,exactLowerFamilyCode⟩

#print axioms residualCalibration

end LogicLineages.PermittedControl.RawPacketAlgebra
