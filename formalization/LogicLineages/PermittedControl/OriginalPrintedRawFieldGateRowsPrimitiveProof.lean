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
    simp only [id_eq]
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

private theorem sourcePrimitive : Primrec (fun g : RawGate => g.2.1) :=
  Primrec.fst.comp Primrec.snd

private theorem outputPrimitive : Primrec (fun g : RawGate => g.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem payloadPrimitive : Primrec (fun g : RawGate => g.2.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

private theorem headPrimitive : Primrec (fun g : RawGate => g.2.2.2.1.1) :=
  Primrec.fst.comp payloadPrimitive

private theorem endpointPrimitive : Primrec (fun g : RawGate => g.2.2.2.1.2) :=
  Primrec.snd.comp payloadPrimitive

private theorem iterateOperandPrimitive : Primrec (fun g : RawGate =>
    ((1,g.2.1,(0,g.2.2.2.1.1,0,0)) : LowerOperandCode)) :=
  (Primrec.const 1).pair (sourcePrimitive.pair
    ((Primrec.const 0).pair (headPrimitive.pair (Primrec.const (0,0)))))

private theorem properOperandPrimitive (k : Nat) : Primrec (fun g : RawGate =>
    ((k,g.2.1,(1,0,g.2.2.2.1.1,g.2.2.2.1.2)) : LowerOperandCode)) :=
  (Primrec.const k).pair (sourcePrimitive.pair ((Primrec.const 1).pair
    ((Primrec.const 0).pair (headPrimitive.pair endpointPrimitive))))

private theorem onePrimitive {operand : RawGate → LowerOperandCode} (h : Primrec operand) :
    Primrec (fun g : RawGate => some [equalityCode (operand g) g.2.2.1]) :=
  Primrec.option_some.comp
    (Primrec.list_cons.comp (equalityPrimitive.comp h outputPrimitive) (Primrec.const []))

private def identityInput (g : RawGate) : Nat × Nat × Nat :=
  (g.2.2.2.1.1, g.2.1, g.2.2.1)

private theorem identityInputPrimitive : Primrec identityInput :=
  headPrimitive.pair (sourcePrimitive.pair outputPrimitive)

private def identityOutput (b : Bool) (p : Nat × Nat × Nat) : List RawRow :=
  identityRowsCode b p.1 p.2.1 p.2.2

private theorem identityOutputPrimitive (b : Bool) : Primrec (identityOutput b) :=
  identityPrimitive b

private theorem identityCompositePrimitive (b : Bool) :
    Primrec (identityOutput b ∘ identityInput) :=
  (identityOutputPrimitive b).comp identityInputPrimitive

private theorem optionLiftPrimitive {A T : Type} [Primcodable A] [Primcodable T]
    {f : A → T} (h : Primrec f) : Primrec (fun a => some (f a)) :=
  Primrec.option_some.comp h

private theorem identityCaseLiteral (b : Bool) (g : RawGate) :
    some ((identityOutput b ∘ identityInput) g) =
      some (identityRowsCode b g.2.2.2.1.1 g.2.1 g.2.2.1) := rfl

private theorem identityCasePrimitive (b : Bool) : Primrec (fun g : RawGate =>
    some (identityRowsCode b g.2.2.2.1.1 g.2.1 g.2.2.1)) :=
  (optionLiftPrimitive (identityCompositePrimitive b)).of_eq (identityCaseLiteral b)

private theorem dispatchPrimitive {A T : Type} [Primcodable A] [Primcodable T]
    {tag : A → Nat} {on2 on3 on4 on5 on6 : A → Option T}
    (ht : Primrec tag) (h2 : Primrec on2) (h3 : Primrec on3) (h4 : Primrec on4)
    (h5 : Primrec on5) (h6 : Primrec on6) :
    Primrec (fun a : A => if tag a = 2 then on2 a else if tag a = 3 then on3 a
      else if tag a = 4 then on4 a else if tag a = 5 then on5 a
      else if tag a = 6 then on6 a else none) := by
  have eq (k : Nat) : PrimrecPred (fun a : A => tag a = k) :=
    Primrec.eq.comp ht (Primrec.const k)
  exact Primrec.ite (eq 2) h2 (Primrec.ite (eq 3) h3 (Primrec.ite (eq 4) h4
    (Primrec.ite (eq 5) h5 (Primrec.ite (eq 6) h6 (Primrec.const none)))))

private theorem rowsPrimitive : Primrec rowsCode := by
  have tag : Primrec (Prod.fst : RawGate → Nat) := Primrec.fst
  exact (dispatchPrimitive tag (onePrimitive iterateOperandPrimitive)
    (onePrimitive (properOperandPrimitive 1)) (onePrimitive (properOperandPrimitive 2))
    (identityCasePrimitive false) (identityCasePrimitive true)).of_eq (fun _ => rfl)

theorem exactOriginalRawFieldGateEffectivity : ExactOriginalRawFieldGateEffectivity := by
  have step : Primrec (fun p : StepArgs × List RawRow => (p.1.1,p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair Primrec.snd
  exact ⟨rowsPrimitive,Primrec.option_map (rowsPrimitive.comp Primrec.snd) step.to₂⟩

end LogicLineages.PermittedControl.OriginalPrintedRawFieldGateRows
