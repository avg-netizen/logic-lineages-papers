module
public import LogicLineages.PermittedControl.StageCallbackRenderLinearTargets
import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingCodePrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackRender
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (add_primitive)
open PreparedProjection (LowerOperandCode PreparedPacketCode)
open MixedSameRankResidue (WeightedCode)
open ActualCanonicalOperandGrouping (groupRaw)
open ActualCanonicalOperandGroupingCode (groupRawPrimitive)
open ActualRawSignedStaticCeiling (RawSyntax)

theorem lowerPrimitive : Primrec₂ lowerCode := by
  let A := Nat × List WeightedCode
  have rank : Primrec (fun q : A × (WeightedCode × List WeightedCode) => q.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have step : Primrec (fun q : A × (WeightedCode × List WeightedCode) =>
      if q.2.1.2.2.1 < q.1.1 then q.2.1 :: q.2.2 else q.2.2) :=
    Primrec.ite (Primrec.nat_lt.comp rank (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have fold : Primrec (fun q : A =>
      q.2.foldr (fun t rest => if t.2.2.1 < q.1 then t :: rest else rest) []) :=
    Primrec.list_foldr Primrec.snd (Primrec.const []) step.to₂
  exact fold.to₂

theorem slopePrimitive : Primrec₂ slopeCode := by
  let A := Nat × List WeightedCode
  have rank : Primrec (fun q : A × (WeightedCode × Int) => q.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
  have step : Primrec (fun q : A × (WeightedCode × Int) =>
      if q.2.1.2.2.1 = q.1.1 then q.2.1.1 + q.2.2 else q.2.2) :=
    Primrec.ite (Primrec.eq.comp rank (Primrec.fst.comp Primrec.fst))
      (add_primitive.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have fold : Primrec (fun q : A =>
      q.2.foldr (fun t acc => if t.2.2.1 = q.1 then t.1 + acc else acc) (0 : Int)) :=
    Primrec.list_foldr Primrec.snd (Primrec.const (0 : Int)) step.to₂
  exact fold.to₂

theorem namesPrimitive : Primrec₂ namesCode := by
  let I := Int × NormalForm.Code.ItemData
  let A := Nat × List WeightedCode
  let S := Nat × List I
  have item : Primrec (fun q : A × (S × WeightedCode) =>
      ((q.2.2.1,((0 : Nat),q.2.1.1,(0 : Int),(0 : Int))) : I)) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      ((Primrec.const (0 : Nat)).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          (Primrec.const ((0 : Int),(0 : Int)))))
  have step : Primrec (fun q : A × (S × WeightedCode) =>
      ((q.2.1.1+1,q.2.1.2 ++ [(q.2.2.1,((0 : Nat),q.2.1.1,(0 : Int),(0 : Int)))]) : S)) :=
    (Primrec.succ.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))).pair
      (Primrec.list_append.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.list_cons.comp item (Primrec.const [])))
  have fold : Primrec (fun q : A =>
      q.2.foldl (fun st t => (st.1+1,st.2 ++ [(t.1,((0 : Nat),st.1,(0 : Int),(0 : Int)))]))
        (q.1,([] : List I))) :=
    Primrec.list_foldl Primrec.snd (Primrec.fst.pair (Primrec.const [])) step.to₂
  exact (Primrec.snd.comp fold).to₂

theorem rowPrimitive :
    Primrec (fun p : Nat × Int × List WeightedCode => rowCode p.1 p.2.1 p.2.2) := by
  let A := Nat × Int × List WeightedCode
  have ts : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have slope : Primrec (fun p : A => slopeCode p.1 p.2.2) := slopePrimitive.comp Primrec.fst ts
  have low : Primrec (fun p : A => lowerCode p.1 p.2.2) := lowerPrimitive.comp Primrec.fst ts
  have names : Primrec (fun p : A => namesCode 1 (lowerCode p.1 p.2.2)) :=
    namesPrimitive.comp (Primrec.const 1) low
  have head : Primrec (fun p : A =>
      ((slopeCode p.1 p.2.2,((0 : Nat),(0 : Nat),(0 : Int),(0 : Int))) :
        Int × NormalForm.Code.ItemData)) :=
    slope.pair (Primrec.const _)
  exact (Primrec.fst.comp Primrec.snd).pair (Primrec.list_cons.comp head names)

theorem atomPrimitive : Primrec atomCode := by
  have data : Primrec (fun r : NormalForm.Code.RowData =>
      (((0 : Nat),(0 : Nat),r) : NormalForm.Code.AtomData)) :=
    (Primrec.const (0 : Nat)).pair ((Primrec.const (0 : Nat)).pair Primrec.id)
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp data)) (Primrec.const 2)

theorem testPrimitive : Primrec₂ testCode := by
  let A := Nat × NormalForm.Code.RowData
  have scaled : Primrec (fun q : A => LinearRows.Code.rowScale (-1) q.2) :=
    LinearRowsCodeProof.rowScale_primitive.comp (Primrec.const (-1 : Int)) Primrec.snd
  have equal : Primrec (fun q : A => LinearRows.Code.conjunction (atomCode q.2)
      (atomCode (LinearRows.Code.rowScale (-1) q.2))) :=
    LinearRowsCodeProof.conjunction_primitive.comp (atomPrimitive.comp Primrec.snd)
      (atomPrimitive.comp scaled)
  have lowered : Primrec (fun q : A => ((q.2.1 - 1,q.2.2) : NormalForm.Code.RowData)) :=
    ((add_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.const (-1 : Int))).of_eq
      (fun q => by omega)).pair (Primrec.snd.comp Primrec.snd)
  have body : Primrec (fun q : A =>
      if q.1 = 0 then
        LinearRows.Code.conjunction (atomCode q.2) (atomCode (LinearRows.Code.rowScale (-1) q.2))
      else if q.1 = 1 then atomCode q.2
      else atomCode (q.2.1 - 1,q.2.2)) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) equal
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1)) (atomPrimitive.comp Primrec.snd)
        (atomPrimitive.comp lowered))
  exact body.to₂

theorem linearPrimitive :
    Primrec (fun p : Nat × RawSyntax × Nat × Bool => linearCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := Nat × RawSyntax × Nat × Bool
  have g : Primrec (fun p : A => groupRaw p.2.1.2) :=
    groupRawPrimitive.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have low : Primrec (fun p : A => lowerCode p.1 (groupRaw p.2.1.2)) :=
    lowerPrimitive.comp Primrec.fst g
  have table : Primrec (fun p : A =>
      Encodable.encode ((lowerCode p.1 (groupRaw p.2.1.2)).map Prod.snd)) :=
    Primrec.encode.comp (Primrec.list_map low (Primrec.snd.comp Primrec.snd).to₂)
  have row : Primrec (fun p : A => rowCode p.1 p.2.1.1 (groupRaw p.2.1.2)) :=
    rowPrimitive.comp (Primrec.fst.pair ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair g))
  have test : Primrec (fun p : A =>
      testCode p.2.2.1 (rowCode p.1 p.2.1.1 (groupRaw p.2.1.2))) :=
    testPrimitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) row
  have polarity : Primrec (fun p : A =>
      polarityCode (testCode p.2.2.1 (rowCode p.1 p.2.1.1 (groupRaw p.2.1.2))) p.2.2.2) :=
    Primrec.cond (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) test
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) test) (Primrec.const 3))
  exact table.pair polarity

theorem linearCodeEffectivity : LinearCodeEffectivity :=
  ⟨lowerPrimitive,slopePrimitive,namesPrimitive,rowPrimitive,testPrimitive,linearPrimitive⟩

end LogicLineages.PermittedControl.StageCallbackRender
