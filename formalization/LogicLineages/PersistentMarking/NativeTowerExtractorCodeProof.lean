module
public import LogicLineages.PersistentMarking.NativeTowerExtractorCodeKernel
public import LogicLineages.PersistentMarking.NativeTowerIteratorCodeProof
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerExtractorCodeProof
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerTypeCodeProof (nativeTowerTypeCodeEffectivity)
open NativeTowerEraseCodeKernel (boundCode lambdaCode)
open NativeTowerEraseCodeProof (boundCodePrimitive lambdaCodePrimitive)
open NativeTowerIteratorCodeKernel (applicationCode iteratorCode)
open NativeTowerIteratorCodeProof (applicationPrimitive iteratorPrimitive)
open NativeTowerExtractorCodeKernel

private theorem fourInputs {T : Type} [Primcodable T] {a b f x : T → Nat}
    (ha : Primrec a) (hb : Primrec b) (hf : Primrec f) (hx : Primrec x) :
    Primrec (fun p => (a p,b p,f p,x p)) := by
  have tail : Primrec (fun p => (b p,f p,x p)) := hb.pair (hf.pair hx)
  exact ha.pair tail

private theorem composeFour {T : Type} [Primcodable T] {a b f x : T → Nat}
    {raw : (Nat × Nat × Nat × Nat) → Nat} (h : Primrec raw)
    (ha : Primrec a) (hb : Primrec b) (hf : Primrec f) (hx : Primrec x) :
    Primrec (fun p => raw (a p,b p,f p,x p)) :=
  h.comp (fourInputs ha hb hf hx)

private theorem makeApp {T : Type} [Primcodable T] {a b f x : T → Nat}
    (ha : Primrec a) (hb : Primrec b) (hf : Primrec f) (hx : Primrec x) :
    Primrec (fun p => applicationCode (a p) (b p) (f p) (x p)) :=
  composeFour applicationPrimitive ha hb hf hx

private theorem levelShift {T : Type} [Primcodable T] {f : T → Nat}
    (hf : Primrec f) (k : Nat) : Primrec (fun p => typeCode (f p+k)) :=
  nativeTowerTypeCodeEffectivity.comp (Primrec.nat_add.comp hf (Primrec.const k))

theorem lowerOperandPrimitive : Primrec lowerOperandCode :=
  Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const ordinalZeroCode) (boundCodePrimitive.comp nativeTowerTypeCodeEffectivity Primrec.id)

private theorem drainStepPrimitive : Primrec₂ drainStep := by
  let T := Nat × Nat
  have j : Primrec (Prod.fst : T → Nat) := Primrec.fst
  have t := nativeTowerTypeCodeEffectivity.comp j
  have arg := lowerOperandPrimitive.comp j
  exact (makeApp t t (Primrec.snd : Primrec (Prod.snd : T → Nat)) arg).to₂

theorem drainPrimitive : Primrec₂ drainCode := by
  let T := Nat × Nat
  let U := T × (Nat × Nat)
  have j : Primrec (fun p : U => p.2.1) := Primrec.fst.comp Primrec.snd
  have q : Primrec (fun p : U => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec₂ (fun (_ : T) (p : Nat × Nat) => drainStep p.1 p.2) :=
    (drainStepPrimitive.comp j q).to₂
  exact (Primrec.list_foldr (Primrec.list_range.comp Primrec.fst) Primrec.snd step).to₂

theorem appliedPrimitive : Primrec (fun p : Nat × Nat × Nat × Nat =>
    appliedCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let T := Nat × Nat × Nat × Nat
  have n : Primrec (Prod.fst : T → Nat) := Primrec.fst
  have args : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  have i : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have h : Primrec (fun p : T => p.2.2.1) := Primrec.fst.comp args
  have x : Primrec (fun p : T => p.2.2.2) := Primrec.snd.comp args
  have a := nativeTowerTypeCodeEffectivity.comp n
  have e := levelShift n 1
  have f := makeApp (Primrec.const (typeCode 0)) (levelShift n 2) (iteratorPrimitive.comp n) i
  have g := makeApp e e f h
  exact makeApp a a g x

private theorem initialHPrimitive : Primrec (fun n => boundCode (typeCode (n+1)) (n+1)) :=
  boundCodePrimitive.comp (levelShift Primrec.id 1) Primrec.succ

private theorem innerSeedPrimitive : Primrec (fun n =>
    appliedCode n (boundCode (typeCode 0) 0) (boundCode (typeCode (n+1)) (n+1))
      (lowerOperandCode n)) :=
  composeFour appliedPrimitive Primrec.id (Primrec.const (boundCode (typeCode 0) 0))
    initialHPrimitive lowerOperandPrimitive

theorem innerPrimitive : Primrec innerCode :=
  drainPrimitive.comp Primrec.id innerSeedPrimitive

private theorem bindRangePrimitive : Primrec (fun p : Nat × Nat × Nat =>
    (List.range p.1).map (p.2.1+·)) := by
  let T := Nat × Nat × Nat
  have j : Primrec (fun p : T × Nat => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.nat_add.comp j Primrec.snd).to₂

theorem bindAscendingPrimitive : Primrec (fun p : Nat × Nat × Nat =>
    bindAscendingCode p.1 p.2.1 p.2.2) := by
  let T := Nat × Nat × Nat
  let U := T × (Nat × Nat)
  have q : Primrec (fun p : U => p.2.1) := Primrec.fst.comp Primrec.snd
  have j : Primrec (fun p : U => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec₂ (fun (_ : T) (p : Nat × Nat) => binderStep p.1 p.2) :=
    (lambdaCodePrimitive.comp (nativeTowerTypeCodeEffectivity.comp j) q).to₂
  exact Primrec.list_foldl bindRangePrimitive (Primrec.snd.comp Primrec.snd) step

theorem extractorPrimitive : Primrec₂ extractorCode := by
  let T := Nat × Nat
  have fix : Primrec (Prod.fst : T → Nat) := Primrec.fst
  have n : Primrec (Prod.snd : T → Nat) := Primrec.snd
  have suffix : Primrec (fun p : T => lambdaCode (typeCode 0) (innerCode p.2)) :=
    lambdaCodePrimitive.comp (Primrec.const (typeCode 0)) (innerPrimitive.comp n)
  have head := makeApp (Primrec.const (typeCode 1)) (Primrec.const (typeCode 1)) fix suffix
  have args : Primrec (fun p : T =>
      (p.2+1,1,applicationCode (typeCode 1) (typeCode 1) p.1 (lambdaCode (typeCode 0) (innerCode p.2)))) :=
    (Primrec.succ.comp n).pair ((Primrec.const 1).pair head)
  exact (bindAscendingPrimitive.comp args).to₂

#print axioms drainPrimitive
#print axioms appliedPrimitive
#print axioms bindAscendingPrimitive
#print axioms extractorPrimitive
end LogicLineages.PersistentMarking.NativeTowerExtractorCodeProof
