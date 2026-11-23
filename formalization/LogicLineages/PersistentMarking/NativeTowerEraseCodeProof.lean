module
public import LogicLineages.PersistentMarking.NativeTowerEraseCodeKernel
public import LogicLineages.PersistentMarking.NativeTowerTypeCodeProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerEraseCodeProof
open NativeTowerEraseCodeKernel
open NativeTowerTypeCodeProof (pairPrimitive nativeTowerTypeCodeEffectivity)

theorem fields2Primitive : Primrec₂ fields2 := by
  let P := Nat × Nat
  have tail : Primrec (fun p : P => NativeTowerTypeCodeTargets.codecPair p.2 0 + 1) :=
    Primrec.succ.comp (pairPrimitive.comp Primrec.snd (Primrec.const 0))
  exact (Primrec.succ.comp (pairPrimitive.comp Primrec.fst tail)).to₂

theorem code2Primitive : Primrec (fun p : Nat × Nat × Nat => code2 p.1 p.2.1 p.2.2) := by
  let P := Nat × Nat × Nat
  have a : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have b : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.succ.comp (pairPrimitive.comp Primrec.fst (fields2Primitive.comp a b))

theorem boundCodePrimitive : Primrec₂ boundCode := by
  have args : Primrec (fun p : Nat × Nat => (1,p.1,p.2)) := (Primrec.const 1).pair Primrec.id
  exact (code2Primitive.comp args).to₂

theorem lambdaCodePrimitive : Primrec₂ lambdaCode := by
  have args : Primrec (fun p : Nat × Nat => (2,p.1,p.2)) := (Primrec.const 2).pair Primrec.id
  exact (code2Primitive.comp args).to₂

theorem wrapPrimitive : Primrec₂ wrap := by
  let P := (Nat × Nat) × Nat × Nat
  have depth : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have prev : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec₂ (fun (_ : Nat × Nat) (x : Nat × Nat) =>
      lambdaCode (NativeTowerTypeCodeTargets.typeCode x.1) x.2) :=
    (lambdaCodePrimitive.comp (nativeTowerTypeCodeEffectivity.comp depth) prev).to₂
  exact (Primrec.nat_rec' Primrec.fst Primrec.snd step).to₂

theorem eraseCodePrimitive : Primrec₂ eraseCode := by
  let P := Nat × Nat
  have slot : Primrec (fun p : P => p.2+p.1) := Primrec.nat_add.comp Primrec.snd Primrec.fst
  have seed : Primrec (fun p : P => boundCode (NativeTowerTypeCodeTargets.typeCode 0) (p.2+p.1)) :=
    boundCodePrimitive.comp (Primrec.const _) slot
  exact (wrapPrimitive.comp Primrec.fst seed).to₂

#print axioms fields2Primitive
#print axioms code2Primitive
#print axioms boundCodePrimitive
#print axioms lambdaCodePrimitive
#print axioms wrapPrimitive
#print axioms eraseCodePrimitive
end LogicLineages.PersistentMarking.NativeTowerEraseCodeProof
