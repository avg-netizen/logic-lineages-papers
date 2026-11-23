module
public import LogicLineages.PersistentMarking.NativeTowerEffectiveCodeKernel
public import LogicLineages.PersistentMarking.NativeTowerExtractorCodeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerEffectiveCodeProof
open NativeTowerEffectiveCodeKernel
open NativeTowerTypeCodeTargets (typeCode)
open NativeTowerTypeCodeProof (nativeTowerTypeCodeEffectivity)
open NativeTowerIteratorCodeProof (applicationPrimitive)
open NativeTowerExtractorCodeProof (extractorPrimitive)

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

private theorem threeInputs {T : Type} [Primcodable T] {a b c : T → Nat}
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun p => (a p,b p,c p)) := by
  have tail : Primrec (fun p => (b p,c p)) := hb.pair hc
  exact ha.pair tail

private theorem composeThree {T : Type} [Primcodable T] {a b c : T → Nat}
    {raw : (Nat × Nat × Nat) → Nat} (h : Primrec raw)
    (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
    Primrec (fun p => raw (a p,b p,c p)) :=
  h.comp (threeInputs ha hb hc)

theorem homogeneousPrimitive : Primrec (fun p : Nat × Nat × Nat => homogeneous p.1 p.2.1 p.2.2) := by
  let T := Nat × Nat × Nat
  have ty : Primrec (fun p : T => typeCode p.1) :=
    nativeTowerTypeCodeEffectivity.comp Primrec.fst
  have f : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have x : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  exact composeFour applicationPrimitive ty ty f x

private theorem makeHomogeneous {T : Type} [Primcodable T] {j f x : T → Nat}
    (hj : Primrec j) (hf : Primrec f) (hx : Primrec x) :
    Primrec (fun p => homogeneous (j p) (f p) (x p)) :=
  composeThree homogeneousPrimitive hj hf hx

private theorem lowerStepPrimitive : Primrec (fun p : Nat × Nat × Nat => lowerStep p.1 p.2.1 p.2.2) := by
  let T := Nat × Nat × Nat
  have j : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have h : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  have e : Primrec (fun p : T => NativeTowerExtractorCodeKernel.extractorCode p.1 p.2.1) :=
    extractorPrimitive.comp Primrec.fst j
  exact makeHomogeneous (Primrec.nat_add.comp j (Primrec.const 2)) h e

theorem lowerPrimitive : Primrec (fun p : Nat × Nat × Nat => lower p.1 p.2.1 p.2.2) := by
  let T := Nat × Nat × Nat
  let U := T × Nat × Nat
  have fix : Primrec (fun p : U => p.1.1) := Primrec.fst.comp Primrec.fst
  have pair : Primrec (fun p : U => (p.2.1,p.2.2)) := Primrec.snd
  have step : Primrec₂ (fun (p : T) (j : Nat × Nat) => lowerStep p.1 j.1 j.2) :=
    (lowerStepPrimitive.comp (fix.pair pair)).to₂
  have n : Primrec (fun p : T => p.2.1) := Primrec.fst.comp Primrec.snd
  have seed : Primrec (fun p : T => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr (Primrec.list_range.comp n) seed step

private theorem nbPrimitive : Primrec (fun p : Fixed => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem omegaPrimitive : Primrec (fun p : Fixed => p.2.2) := Primrec.snd.comp Primrec.snd

theorem zeroPrimitive : Primrec NativeTowerEffectiveCodeKernel.zero :=
  makeHomogeneous (Primrec.const 0) nbPrimitive omegaPrimitive

private theorem prefixPrimitive : Primrec (fun p : Fixed × Nat =>
    lower p.1.1 p.2 (NativeTowerExtractorCodeKernel.extractorCode p.1.1 p.2)) := by
  let T := Fixed × Nat
  have c : Primrec (fun p : T => p.1.1) := Primrec.fst.comp Primrec.fst
  have j : Primrec (Prod.snd : T → Nat) := Primrec.snd
  have e := extractorPrimitive.comp c j
  exact composeThree lowerPrimitive c j e

private theorem withNBPrimitive : Primrec (fun p : Fixed × Nat =>
    homogeneous 1 (lower p.1.1 p.2 (NativeTowerExtractorCodeKernel.extractorCode p.1.1 p.2)) p.1.2.1) :=
  makeHomogeneous (Primrec.const 1) prefixPrimitive (nbPrimitive.comp Primrec.fst)

theorem laterPrimitive : Primrec₂ NativeTowerEffectiveCodeKernel.later :=
  (makeHomogeneous (Primrec.const 0) withNBPrimitive (zeroPrimitive.comp Primrec.fst)).to₂

theorem generatePrimitive : Primrec₂ generate := by
  let T := Fixed × Nat
  have c : Primrec (Prod.fst : T → Fixed) := Primrec.fst
  have n : Primrec (Prod.snd : T → Nat) := Primrec.snd
  have z : Primrec (fun p : T => NativeTowerEffectiveCodeKernel.zero p.1) := zeroPrimitive.comp c
  have o : Primrec (fun p : T => homogeneous 0 p.1.2.1 (NativeTowerEffectiveCodeKernel.zero p.1)) :=
    makeHomogeneous (Primrec.const 0) (nbPrimitive.comp c) z
  have rest : Primrec (fun p : T => NativeTowerEffectiveCodeKernel.later p.1 (p.2-2)) :=
    laterPrimitive.comp c (Primrec.nat_sub.comp n (Primrec.const 2))
  exact (Primrec.ite (Primrec.eq.comp n (Primrec.const 0)) z
    (Primrec.ite (Primrec.eq.comp n (Primrec.const 1)) o rest)).to₂

/-- Fixing any actual natural fields gives a primitive recursive index-only program. -/
theorem fixedGeneratorPrimitive (c : Fixed) : Primrec (generate c) :=
  generatePrimitive.comp (Primrec.const c) Primrec.id

#print axioms homogeneousPrimitive
#print axioms lowerPrimitive
#print axioms generatePrimitive
#print axioms fixedGeneratorPrimitive
end LogicLineages.PersistentMarking.NativeTowerEffectiveCodeProof
