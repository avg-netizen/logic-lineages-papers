module
public import LogicLineages.PersistentMarking.NativeTowerIteratorCodeKernel
public import LogicLineages.PersistentMarking.NativeTowerEraseCodeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerIteratorCodeProof
open NativeTowerTypeCodeTargets (codecPair typeCode)
open NativeTowerTypeCodeProof (pairPrimitive nativeTowerTypeCodeEffectivity)
open NativeTowerEraseCodeKernel (code2 fields2 boundCode lambdaCode eraseCode)
open NativeTowerEraseCodeProof (code2Primitive fields2Primitive boundCodePrimitive
  lambdaCodePrimitive eraseCodePrimitive)
open NativeTowerIteratorCodeKernel

theorem arrowPrimitive : Primrec₂ arrowCode :=
  (Primrec.succ.comp pairPrimitive).to₂

private theorem appHeadPrimitive : Primrec₂ (fun a b => codecPair 4 (codecPair a b)) :=
  (pairPrimitive.comp (Primrec.const 4) pairPrimitive).to₂

private theorem twoFields {T : Type} [Primcodable T] {a b : T → Nat}
    (ha : Primrec a) (hb : Primrec b) (k : Nat) :
    Primrec (fun p => code2 k (a p) (b p)) :=
  code2Primitive.comp ((Primrec.const k).pair (ha.pair hb))

theorem applicationPrimitive :
    Primrec (fun p : Nat × Nat × Nat × Nat => applicationCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let T := Nat × Nat × Nat × Nat
  have x : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have arg : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  have header : Primrec (fun p : T => codecPair 4 (codecPair p.1 p.2.1)) :=
    appHeadPrimitive.comp Primrec.fst x
  have body : Primrec (fun p : T => fields2 p.2.2.1 p.2.2.2) :=
    fields2Primitive.comp (Primrec.fst.comp arg) (Primrec.snd.comp arg)
  exact twoFields header body 4

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

private theorem buildApp {T : Type} [Primcodable T] {a b f x : T → Nat}
    (ha : Primrec a) (hb : Primrec b) (hf : Primrec f) (hx : Primrec x) :
    Primrec (fun p => applicationCode (a p) (b p) (f p) (x p)) :=
  composeFour applicationPrimitive ha hb hf hx

private theorem recHeadPrimitive : Primrec recHeadCode :=
  twoFields (pairPrimitive.comp (Primrec.const 3) Primrec.id) (Primrec.const 0) 4

theorem recursorPrimitive : Primrec (fun p : Nat × Nat × Nat × Nat =>
    recursorCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let T := Nat × Nat × Nat × Nat
  have a : Primrec (Prod.fst : T → Nat) := Primrec.fst
  have z : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have rest : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  have k : Primrec (fun p : T => p.2.2.1) := Primrec.fst.comp rest
  have u : Primrec (fun p : T => p.2.2.2) := Primrec.snd.comp rest
  have endo : Primrec (fun p : T => arrowCode p.1 p.1) := arrowPrimitive.comp a a
  have step : Primrec (fun p : T => arrowCode 0 (arrowCode p.1 p.1)) :=
    arrowPrimitive.comp (Primrec.const 0) endo
  have r₁ := buildApp (Primrec.const 0) (arrowPrimitive.comp step endo) (recHeadPrimitive.comp a) z
  have r₂ := buildApp step endo r₁ k
  exact buildApp a a r₂ u

private theorem discardPrimitive : Primrec discardCode :=
  lambdaCodePrimitive.comp Primrec.id
    (lambdaCodePrimitive.comp Primrec.id (boundCodePrimitive.comp Primrec.id (Primrec.const 1)))

private theorem leftPrimitive : Primrec₂ leftCode := by
  let T := Nat × Nat
  have a : Primrec (Prod.fst : T → Nat) := Primrec.fst
  have b : Primrec (Prod.snd : T → Nat) := Primrec.snd
  exact (buildApp a (arrowPrimitive.comp a a) (discardPrimitive.comp a) b).to₂

private theorem typeSucc : Primrec (fun n => typeCode (n+1)) :=
  nativeTowerTypeCodeEffectivity.comp Primrec.succ

private theorem stepPrimitive : Primrec (fun n =>
    applicationCode (typeCode (n+1)) (typeCode (n+1))
      (leftCode (typeCode (n+1)) (boundCode (typeCode (n+1)) 2)) (eraseCode (n+1) 3)) := by
  have seen := boundCodePrimitive.comp typeSucc (Primrec.const 2)
  have left := leftPrimitive.comp typeSucc seen
  have erased := eraseCodePrimitive.comp Primrec.succ (Primrec.const 3)
  exact buildApp typeSucc typeSucc left erased

private theorem iteratorTerminalPrimitive : Primrec (fun n => boundCode (typeCode n) 0) :=
  boundCodePrimitive.comp nativeTowerTypeCodeEffectivity (Primrec.const 0)

private theorem iteratorBodyStepPrimitive : Primrec (fun n => lambdaCode 0
    (applicationCode (typeCode (n+1)) (typeCode (n+1))
      (leftCode (typeCode (n+1)) (boundCode (typeCode (n+1)) 2)) (eraseCode (n+1) 3))) :=
  lambdaCodePrimitive.comp (Primrec.const 0) stepPrimitive

theorem iteratorBodyPrimitive : Primrec iteratorBodyCode :=
  composeFour recursorPrimitive nativeTowerTypeCodeEffectivity (Primrec.const zeroCode)
    iteratorBodyStepPrimitive iteratorTerminalPrimitive

theorem iteratorPrimitive : Primrec iteratorCode :=
  lambdaCodePrimitive.comp (Primrec.const (typeCode 0))
    (lambdaCodePrimitive.comp typeSucc
      (lambdaCodePrimitive.comp nativeTowerTypeCodeEffectivity iteratorBodyPrimitive))

#print axioms applicationPrimitive
#print axioms recursorPrimitive
#print axioms iteratorBodyPrimitive
#print axioms iteratorPrimitive
end LogicLineages.PersistentMarking.NativeTowerIteratorCodeProof
