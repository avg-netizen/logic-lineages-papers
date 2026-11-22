module
public import LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRowsTargets
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
open OrdinalComparison
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (ofNat_primitive negate_primitive)
open HeterogeneousSignedMatrixSlice (RawRow TestCode)
open MixedSameRankResidue (WeightedCode)
open PreparedProjection (LowerOperandCode)
open OriginalPrintedCircuitNumericRead (RawGate)
open OriginalPrintedRawBaseGateRows (coordinateCode normGuardCode StepArgs)

private theorem coordinatePrimitive : Primrec coordinateCode :=
  (Primrec.const 0).pair (Primrec.id.pair (Primrec.const (0,0,0,0)))

private theorem outputTermPrimitive : Primrec (fun output : Nat => ((-1,coordinateCode output) : WeightedCode)) :=
  (Primrec.const (-1)).pair coordinatePrimitive

private theorem equalityPrimitive : Primrec₂ equalityCode := by
  let A := LowerOperandCode × Nat
  have out : Primrec (fun p : A => ((-1,coordinateCode p.2) : WeightedCode)) :=
    outputTermPrimitive.comp Primrec.snd
  have pos : Primrec (fun p : A => ((1,p.1) : WeightedCode)) :=
    (Primrec.const 1).pair Primrec.fst
  have r : Primrec (fun p : A => equalityCode p.1 p.2) :=
    (Primrec.const ((0,0) : TestCode)).pair ((Primrec.const 0).pair
      (Primrec.list_cons.comp out (Primrec.list_cons.comp pos (Primrec.const []))))
  exact r.to₂

private theorem zeroPrimitive : Primrec zeroCode :=
  (Primrec.const ((0,0) : TestCode)).pair ((Primrec.const 0).pair
    (Primrec.list_cons.comp outputTermPrimitive (Primrec.const [])))

private theorem shapePrimitive : Primrec identityShapeCode := by
  have enabled := terminalEntryScanGuardExact.1.comp (Primrec.id.pair Primrec.id)
  have constant : Primrec (fun head : Nat => (if terminalScanGuard (head,head) then 0 else 1 : Int)) := by
    apply (Primrec.cond enabled (Primrec.const 0) (Primrec.const 1)).of_eq
    intro head
    cases terminalScanGuard (head,head) <;> rfl
  exact (Primrec.const ((0,0) : TestCode)).pair (constant.pair (Primrec.const []))

private theorem normPrimitive : Primrec₂ normGuardCode := by
  let A := Nat × Nat
  have m : Primrec (fun p : A => rawNormCode p.1) :=
    (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp Primrec.fst
  have c : Primrec (fun p : A => -(rawNormCode p.1 : Int)) :=
    negate_primitive.comp (ofNat_primitive.comp m)
  have a : Primrec (fun p : A => ((1,coordinateCode p.2) : WeightedCode)) :=
    (Primrec.const 1).pair (coordinatePrimitive.comp Primrec.snd)
  have r : Primrec (fun p : A => normGuardCode p.1 p.2) :=
    (Primrec.const ((1,0) : TestCode)).pair
      (c.pair (Primrec.list_cons.comp a (Primrec.const [])))
  exact r.to₂

private theorem identityPrimitive (count : Bool) : Primrec (fun p : Nat × Nat × Nat =>
    identityRowsCode count p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  have h : Primrec (fun p : A => p.1) := Primrec.fst
  have source : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have o : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have tail (fn : A → RawRow) (hf : Primrec fn) :
      Primrec (fun p : A => [identityShapeCode p.1,normGuardCode p.1 p.2.1,fn p]) :=
    Primrec.list_cons.comp (shapePrimitive.comp h) (Primrec.list_cons.comp (normPrimitive.comp h source)
      (Primrec.list_cons.comp hf (Primrec.const [])))
  cases count with
  | false => exact tail _ (equalityPrimitive.comp (coordinatePrimitive.comp source) o)
  | true => exact tail _ (zeroPrimitive.comp o)

private theorem rowsPrimitive : Primrec rowsCode := by
  have tag : Primrec (fun g : RawGate => g.1) := Primrec.fst
  have source : Primrec (fun g : RawGate => g.2.1) := Primrec.fst.comp Primrec.snd
  have output : Primrec (fun g : RawGate => g.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have payload : Primrec (fun g : RawGate => g.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have head : Primrec (fun g : RawGate => g.2.2.2.1.1) := Primrec.fst.comp payload
  have endpoint : Primrec (fun g : RawGate => g.2.2.2.1.2) := Primrec.snd.comp payload
  have it : Primrec (fun g : RawGate => ((1,g.2.1,(0,g.2.2.2.1.1,0,0)) : LowerOperandCode)) :=
    (Primrec.const 1).pair (source.pair ((Primrec.const 0).pair (head.pair (Primrec.const (0,0)))))
  have proper (k : Nat) : Primrec (fun g : RawGate =>
      ((k,g.2.1,(1,0,g.2.2.2.1.1,g.2.2.2.1.2)) : LowerOperandCode)) :=
    (Primrec.const k).pair (source.pair ((Primrec.const 1).pair
      ((Primrec.const 0).pair (head.pair endpoint))))
  have one {field : RawGate → LowerOperandCode} (h : Primrec field) :
      Primrec (fun g : RawGate => some [equalityCode (field g) g.2.2.1]) :=
    Primrec.option_some.comp (Primrec.list_cons.comp (equalityPrimitive.comp h output) (Primrec.const []))
  have identity (b : Bool) : Primrec (fun g : RawGate =>
      some (identityRowsCode b g.2.2.2.1.1 g.2.1 g.2.2.1)) :=
    Primrec.option_some.comp ((identityPrimitive b).comp (head.pair (source.pair output)))
  have check (k : Nat) : PrimrecPred (fun g : RawGate => g.1 = k) :=
    Primrec.eq.comp tag (Primrec.const k)
  exact Primrec.ite (check 2) (one it) (Primrec.ite (check 3) (one (proper 1))
    (Primrec.ite (check 4) (one (proper 2)) (Primrec.ite (check 5) (identity false)
      (Primrec.ite (check 6) (identity true) (Primrec.const none)))))

theorem exactOriginalRawFieldGateEffectivity : ExactOriginalRawFieldGateEffectivity := by
  have step : Primrec (fun p : StepArgs × List RawRow => (p.1.1,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  exact ⟨rowsPrimitive,Primrec.option_map (rowsPrimitive.comp Primrec.snd) step.to₂⟩

end LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
