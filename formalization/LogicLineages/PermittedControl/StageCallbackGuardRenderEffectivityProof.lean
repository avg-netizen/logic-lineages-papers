module
public import LogicLineages.PermittedControl.StageCallbackGuardRenderTargets
import LogicLineages.PermittedControl.RawPacketAlgebraJoinEffectivityProof
import LogicLineages.PermittedControl.HighFieldPreparedActualStatementChecks
import LogicLineages.PermittedControl.HighFieldComparisonStatementChecks
import LogicLineages.PermittedControl.RawFieldComparisonFormStatementChecks
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof
import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof

public section
namespace LogicLineages.PermittedControl.StageCallbackGuardRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open FieldComparison (LongFieldCode)
open RawPacketAlgebra (tableOf appendCode unitCode tablePrimitive appendPrimitive)
open ActualRawComparisonCeiling (LabelCode PairCode orderedPairs)

attribute [local irreducible] HighFieldPreparedPacket.compile FieldComparison.rawSameForm
  FieldComparison.normalizeHighFieldCode RawPacketAlgebra.appendCode RawPacketAlgebra.tableOf
  LinearRows.Code.conjunction

abbrev FiveCode := LongFieldCode × LongFieldCode × Nat × Nat × Nat

theorem slotPrimitive : Primrec slotCode :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const _))

theorem orderGuardPrimitive : Primrec orderGuardCode := by
  have data : Primrec (fun n : Nat => (((0 : Nat),(0 : Nat),((-1 : Int),
      [((1 : Int),((0 : Nat),(0 : Nat),(0 : Int),(0 : Int))),
       ((-1 : Int),((0 : Nat),n,(0 : Int),(0 : Int)))])) : NormalForm.Code.AtomData)) :=
    (Primrec.const _).pair ((Primrec.const _).pair ((Primrec.const _).pair
      (Primrec.list_cons.comp (Primrec.const _)
        (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair
          (Primrec.id.pair (Primrec.const _)))) (Primrec.const [])))))
  have h := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp data))
    (Primrec.const 2)
  exact h

theorem strictFromBasePrimitive : Primrec₂ strictFromBase := by
  have table : Primrec (fun x : Nat × PreparedPacketCode => tableOf x.2.1) :=
    tablePrimitive.comp (Primrec.fst.comp Primrec.snd)
  have slots : Primrec (fun x : Nat × PreparedPacketCode => tableOf x.2.1 ++ [slotCode x.1]) :=
    Primrec.list_append.comp table (Primrec.list_cons.comp (slotPrimitive.comp Primrec.fst) (Primrec.const []))
  have bytes : Primrec (fun x : Nat × PreparedPacketCode =>
      Encodable.encode (tableOf x.2.1 ++ [slotCode x.1])) := Primrec.encode.comp slots
  have guard : Primrec (fun x : Nat × PreparedPacketCode => orderGuardCode ((tableOf x.2.1).length + 1)) :=
    orderGuardPrimitive.comp (Primrec.succ.comp (Primrec.list_length.comp table))
  have conj : Primrec (fun x : Nat × PreparedPacketCode =>
      LinearRows.Code.conjunction (orderGuardCode ((tableOf x.2.1).length + 1)) x.2.2) :=
    LinearRowsCodeProof.conjunction_primitive.comp guard (Primrec.snd.comp Primrec.snd)
  have h := bytes.pair conj
  exact h

theorem strictPrimitive :
    Primrec (fun x : FiveCode => strictCode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have compileP : Primrec HighFieldPreparedPacket.compile :=
    StatementChecks.fixed_highFieldPreparedFullCompilerEffective
  have lo : Primrec (fun x : FiveCode => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h := strictFromBasePrimitive.comp lo compileP
  exact h

theorem constantPrimitive : Primrec₂ constantCode :=
  Primrec.ite (Primrec.eq.comp Primrec.fst Primrec.snd) (Primrec.const 0) (Primrec.const 1)

theorem equalPrimitive :
    Primrec (fun x : LongFieldCode × LongFieldCode × Nat => equalCode x.1 x.2.1 x.2.2) := by
  have normP : Primrec FieldComparison.normalizeHighFieldCode :=
    StatementChecks.fixed_highFieldComparisonEffective.1
  have sameP : Primrec₂ FieldComparison.rawSameForm :=
    StatementChecks.fixed_rawFieldComparisonFormEffective.2
  have form : Primrec (fun x : LongFieldCode × LongFieldCode × Nat =>
      FieldComparison.rawSameForm (FieldComparison.normalizeHighFieldCode x.1)
        (FieldComparison.normalizeHighFieldCode x.2.1)) :=
    sameP.comp (normP.comp Primrec.fst) (normP.comp (Primrec.fst.comp Primrec.snd))
  have code : Primrec (fun x : LongFieldCode × LongFieldCode × Nat =>
      constantCode (FieldComparison.rawSameForm (FieldComparison.normalizeHighFieldCode x.1)
        (FieldComparison.normalizeHighFieldCode x.2.1)) x.2.2) :=
    constantPrimitive.comp form (Primrec.snd.comp Primrec.snd)
  have h := (Primrec.const (Encodable.encode ([] : List LowerOperandCode))).pair code
  exact h

theorem topPrimitive :
    Primrec (fun x : FiveCode => topCode x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  have F : Primrec (fun x : FiveCode => x.1) := Primrec.fst
  have G : Primrec (fun x : FiveCode => x.2.1) := Primrec.fst.comp Primrec.snd
  have i : Primrec (fun x : FiveCode => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have j : Primrec (fun x : FiveCode => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have w : Primrec (fun x : FiveCode => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have swapped : Primrec (fun x : FiveCode =>
      ((x.2.1,x.1,x.2.2.2.1,x.2.2.1,2 - x.2.2.2.2) : FiveCode)) :=
    G.pair (F.pair (j.pair (i.pair (Primrec.nat_sub.comp (Primrec.const 2) w))))
  have reversed : Primrec (fun x : FiveCode => strictCode x.2.1 x.1 x.2.2.2.1 x.2.2.1 (2 - x.2.2.2.2)) := by
    have h := strictPrimitive.comp swapped
    exact h
  have equal : Primrec (fun x : FiveCode => equalCode x.1 x.2.1 x.2.2.2.2) := by
    have h := equalPrimitive.comp (F.pair (G.pair w))
    exact h
  have inner := Primrec.ite (Primrec.nat_lt.comp j i) reversed equal
  have h := Primrec.ite (Primrec.nat_lt.comp i j) strictPrimitive inner
  exact h

theorem lowerFormulaPrimitive : Primrec lowerFormulaCode :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0)) (Primrec.const _)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const _) (Primrec.const _))

theorem lowerPairPrimitive : Primrec₂ lowerPairCode := by
  let A := PairCode × Nat
  have one : Primrec (fun x : A => (((1 : Nat),x.1.1.1,x.1.1.2) : LowerOperandCode)) :=
    (Primrec.const 1).pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
  have two : Primrec (fun x : A => (((1 : Nat),x.1.2.1,x.1.2.2) : LowerOperandCode)) :=
    (Primrec.const 1).pair ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have table : Primrec (fun x : A => Encodable.encode
      ([((1 : Nat),x.1.1.1,x.1.1.2),((1 : Nat),x.1.2.1,x.1.2.2)] : List LowerOperandCode)) :=
    Primrec.encode.comp (Primrec.list_cons.comp one (Primrec.list_cons.comp two (Primrec.const [])))
  have h := table.pair (lowerFormulaPrimitive.comp Primrec.snd)
  exact h

theorem pairPrimitive : Primrec (fun p : Nat × PairCode × Nat => pairCode p.1 p.2.1 p.2.2) := by
  let X := Nat × PairCode × Nat
  have top : Primrec (fun x : X => x.1) := Primrec.fst
  have pr : Primrec (fun x : X => x.2.1) := Primrec.fst.comp Primrec.snd
  have a : Primrec (fun x : X => x.2.2) := Primrec.snd.comp Primrec.snd
  have r1 : Primrec (fun x : X => x.2.1.1.1) := Primrec.fst.comp (Primrec.fst.comp pr)
  have F1 : Primrec (fun x : X => x.2.1.1.2) := Primrec.snd.comp (Primrec.fst.comp pr)
  have r2 : Primrec (fun x : X => x.2.1.2.1) := Primrec.fst.comp (Primrec.snd.comp pr)
  have F2 : Primrec (fun x : X => x.2.1.2.2) := Primrec.snd.comp (Primrec.snd.comp pr)
  have low : Primrec (fun x : X => lowerPairCode x.2.1 x.2.2) := lowerPairPrimitive.comp pr a
  have high : Primrec (fun x : X => topCode x.2.1.1.2 x.2.1.2.2 x.2.1.1.1 x.2.1.2.1 x.2.2) := by
    have h := topPrimitive.comp (F1.pair (F2.pair (r1.pair (r2.pair a))))
    exact h
  have h := Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_max.comp r1 r2) top) low high
  exact h

theorem compileZip (top : Nat) : ∀ (ps : List PairCode) (as : List Nat),
    compileCode top ps as =
      (ps.zip as).foldr (fun q acc => appendCode (pairCode top q.1 q.2) acc)
        (if ps.length = as.length then unitCode else falseCode)
  | [],[] => rfl
  | [],_ :: _ => rfl
  | _ :: _,[] => rfl
  | p :: ps,a :: as => by
    show appendCode (pairCode top p a) (compileCode top ps as) =
      appendCode (pairCode top p a) ((ps.zip as).foldr (fun q acc => appendCode (pairCode top q.1 q.2) acc)
        (if ps.length + 1 = as.length + 1 then unitCode else falseCode))
    rw [compileZip top ps as]
    simp only [Nat.add_right_cancel_iff]

private theorem orderedPairsPrimitive : Primrec orderedPairs := by
  let A := List LabelCode × LabelCode
  let R := A × LabelCode
  have left : Primrec (fun p : R => p.1.2) := Primrec.snd.comp Primrec.fst
  have right : Primrec (fun p : R => p.2) := Primrec.snd
  have one : Primrec (fun p : A => p.1.map (Prod.mk p.2)) :=
    Primrec.list_map Primrec.fst (left.pair right).to₂
  exact Primrec.list_flatMap Primrec.id one.to₂

theorem compilePrimitive :
    Primrec (fun p : Nat × List PairCode × List Nat => compileCode p.1 p.2.1 p.2.2) := by
  let X := Nat × List PairCode × List Nat
  have zipP : Primrec₂ (List.zip : List PairCode → List Nat → List (PairCode × Nat)) :=
    OrdinalComparison.LayeredComparison.CommonHeadCode.Program.zipWith_primitive Prod.mk Primrec₂.pair
  have zipped : Primrec (fun x : X => x.2.1.zip x.2.2) :=
    zipP.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have base : Primrec (fun x : X => if x.2.1.length = x.2.2.length then unitCode else falseCode) :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))) (Primrec.const _) (Primrec.const _)
  have stepPair : Primrec (fun y : X × ((PairCode × Nat) × PreparedPacketCode) =>
      pairCode y.1.1 y.2.1.1 y.2.1.2) := by
    have yTop : Primrec (fun y : X × ((PairCode × Nat) × PreparedPacketCode) => y.1.1) :=
      Primrec.fst.comp Primrec.fst
    have yPair : Primrec (fun y : X × ((PairCode × Nat) × PreparedPacketCode) => y.2.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
    have yAnswer : Primrec (fun y : X × ((PairCode × Nat) × PreparedPacketCode) => y.2.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
    have h := pairPrimitive.comp (yTop.pair (yPair.pair yAnswer))
    exact h
  have step : Primrec₂ (fun (x : X) (y : (PairCode × Nat) × PreparedPacketCode) =>
      appendCode (pairCode x.1 y.1.1 y.1.2) y.2) := by
    have h := appendPrimitive.comp stepPair (Primrec.snd.comp Primrec.snd)
    exact h
  have folded := Primrec.list_foldr zipped base step
  exact folded.of_eq (fun x => (compileZip x.1 x.2.1 x.2.2).symm)

theorem guardPrimitive :
    Primrec (fun p : Nat × List LabelCode × List Nat => guardCode p.1 p.2.1 p.2.2) := by
  have args : Primrec (fun p : Nat × List LabelCode × List Nat =>
      ((p.1,orderedPairs p.2.1,p.2.2) : Nat × List PairCode × List Nat)) :=
    Primrec.fst.pair ((orderedPairsPrimitive.comp (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))
  have h := compilePrimitive.comp args
  exact h

theorem guardCodeEffectivity : GuardCodeEffectivity :=
  ⟨pairPrimitive,compilePrimitive,guardPrimitive⟩

#print axioms guardCodeEffectivity

end LogicLineages.PermittedControl.StageCallbackGuardRender
