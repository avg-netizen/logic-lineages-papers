module
public import LogicLineages.PermittedControl.RawPacketAlgebraReifyTargets
import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyProof
import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyPrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (ofNat_primitive negate_primitive)
open PreparedProjection (LowerOperand LowerOperandCode)
open HeterogeneousSignedMatrixSlice (RawRow encodeRow)
open OriginalProjectedMatrixSemantics (availabilityRows)
open OriginalPrintedTerminalBitClauses (clauses)
open ActualLowerRankChartRows (lowerChart)
open ActualGreatestRouteResidual (Residual)
open ActualGuardedResidualBitFamily (reify reifyFamily)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeBitRow encodeFamily)
open OriginalPrintedRawClauseAssembly (clausesCode exactOriginalRawClauseAssembly
  exactOriginalRawClauseEffectivity)

theorem availabilityCodeEq (ops : List LowerOperand) :
    availabilityCode (ops.map LowerOperand.code) = (availabilityRows ops).map encodeRow := by
  unfold availabilityCode availabilityRows
  rw [List.map_map,List.map_map]
  rfl

theorem exactAvailabilityCode : ExactAvailabilityCode := availabilityCodeEq

theorem lowerChartCodeEq (B top : Nat) : lowerChartCode B top = (lowerChart B top).map encodeBitRow := by
  unfold lowerChartCode lowerChart
  rw [List.map_append,List.map_map,List.map_map]
  rfl

theorem exactLowerChartCode : ExactLowerChartCode := lowerChartCodeEq

theorem reifyCodeEq (C top : Nat) (out : Residual) :
    reifyCode C top (encodeResidual out) = encodeFamily (reify C top out) := by
  change (clausesCode (out.formula.encode,true,availabilityCode (out.ops.map LowerOperand.code),
      out.atoms.map encodeRow)).map (fun row => lowerChartCode C top ++ row) =
    ((clauses (availabilityRows out.ops) out.atoms out.formula true).map
      (fun row => lowerChart C top ++ row)).map (List.map encodeBitRow)
  rw [availabilityCodeEq,exactOriginalRawClauseAssembly (availabilityRows out.ops) out.atoms out.formula true,
    lowerChartCodeEq]
  simp only [encodeFamily,List.map_map,Function.comp_def,List.map_append]

theorem exactReifyCode : ExactReifyCode := reifyCodeEq

theorem reifyFamilyCodeEq (C top : Nat) (outs : List Residual) :
    reifyFamilyCode C top (outs.map encodeResidual) = encodeFamily (reifyFamily C top outs) := by
  induction outs with
  | nil => rfl
  | cons o os ih =>
    show List.flatMap (reifyCode C top) (encodeResidual o :: os.map encodeResidual) =
      encodeFamily (List.flatMap (reify C top) (o :: os))
    rw [List.flatMap_cons,List.flatMap_cons,reifyCodeEq]
    change _ ++ reifyFamilyCode C top (os.map encodeResidual) =
      encodeFamily (reify C top o ++ reifyFamily C top os)
    rw [ih]
    simp only [encodeFamily,List.map_append]

theorem exactReifyFamilyCode : ExactReifyFamilyCode := reifyFamilyCodeEq

theorem reifyCalibration : ReifyCalibration :=
  ⟨exactAvailabilityCode,exactLowerChartCode,exactReifyCode,exactReifyFamilyCode⟩

theorem availabilityPrimitive : Primrec availabilityCode := by
  have g : Primrec₂ (fun (_ : List LowerOperandCode) (op : LowerOperandCode) =>
      ((((1 : Nat),(0 : Nat)),(0 : Int),[((1 : Int),op)]) : RawRow)) :=
    (Primrec.const _).pair ((Primrec.const _).pair
      (Primrec.list_cons.comp ((Primrec.const _).pair Primrec.snd) (Primrec.const [])))
  exact Primrec.list_map Primrec.id g

theorem lowerChartPrimitive : Primrec₂ lowerChartCode := by
  have neg : Primrec (fun B : Nat => -(B : Int)) := negate_primitive.comp ofNat_primitive
  have fund : Primrec₂ (fun (x : Nat × Nat) (i : Nat) =>
      (((((1 : Nat),(0 : Nat)),-(x.1 : Int),
        [((1 : Int),((0 : Nat),i,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat))))]),true) : RawBitRow)) :=
    ((Primrec.const _).pair ((neg.comp (Primrec.fst.comp Primrec.fst)).pair
      (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair
        (Primrec.snd.pair (Primrec.const _)))) (Primrec.const [])))).pair (Primrec.const true)
  have rising : Primrec₂ (fun (_ : Nat × Nat) (i : Nat) =>
      (((((2 : Nat),(0 : Nat)),(0 : Int),
        [((1 : Int),((0 : Nat),i+1,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat)))),
         ((-1 : Int),((0 : Nat),i,((0 : Nat),(0 : Nat),(0 : Nat),(0 : Nat))))]),true) : RawBitRow)) :=
    ((Primrec.const _).pair ((Primrec.const _).pair
      (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair
          ((Primrec.succ.comp Primrec.snd).pair (Primrec.const _))))
        (Primrec.list_cons.comp ((Primrec.const _).pair ((Primrec.const _).pair
          (Primrec.snd.pair (Primrec.const _)))) (Primrec.const []))))).pair (Primrec.const true)
  exact Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_range.comp Primrec.snd) fund)
    (Primrec.list_map (Primrec.list_range.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))) rising)

theorem reifyPrimitive : Primrec (fun x : Nat × Nat × ResidualCode => reifyCode x.1 x.2.1 x.2.2) := by
  let X := Nat × Nat × ResidualCode
  have clausesP : Primrec clausesCode := exactOriginalRawClauseEffectivity.2.2
  have ops : Primrec (fun x : X => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have formula : Primrec (fun x : X => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have atoms : Primrec (fun x : X => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have family : Primrec (fun x : X => clausesCode (x.2.2.2.1,true,availabilityCode x.2.2.1,x.2.2.2.2)) :=
    clausesP.comp (formula.pair ((Primrec.const true).pair ((availabilityPrimitive.comp ops).pair atoms)))
  have g : Primrec₂ (fun (x : X) (row : List RawBitRow) => lowerChartCode x.1 x.2.1 ++ row) :=
    Primrec.list_append.comp
      (lowerChartPrimitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd
  exact Primrec.list_map family g

theorem reifyFamilyPrimitive :
    Primrec (fun x : Nat × Nat × List ResidualCode => reifyFamilyCode x.1 x.2.1 x.2.2) := by
  have g : Primrec₂ (fun (x : Nat × Nat × List ResidualCode) (r : ResidualCode) => reifyCode x.1 x.2.1 r) :=
    reifyPrimitive.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  exact Primrec.list_flatMap (Primrec.snd.comp Primrec.snd) g

theorem reifyEffectivity : ReifyEffectivity :=
  ⟨availabilityPrimitive,lowerChartPrimitive,reifyPrimitive,reifyFamilyPrimitive⟩

theorem fullRawPacketAlgebraReify : FullRawPacketAlgebraReify := ⟨reifyCalibration,reifyEffectivity⟩

#print axioms fullRawPacketAlgebraReify

end LogicLineages.PermittedControl.RawPacketAlgebra
