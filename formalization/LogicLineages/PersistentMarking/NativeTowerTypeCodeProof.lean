module
public import LogicLineages.PersistentMarking.NativeTowerTypeCodeKernel
public import Mathlib.Computability.Primrec.Basic

@[expose] public section
namespace LogicLineages.PersistentMarking.NativeTowerTypeCodeProof
open NativeTowerTypeCodeTargets

theorem pairPrimitive : Primrec₂ codecPair := by
  have add : Primrec (fun p : Nat × Nat => p.1+p.2) :=
    Primrec.nat_add.comp Primrec.fst Primrec.snd
  have square : Primrec (fun p : Nat × Nat => (p.1+p.2)*(p.1+p.2)) :=
    Primrec.nat_mul.comp add add
  exact (Primrec.nat_add.comp square Primrec.fst).to₂

theorem nativeTowerTypeCodeEffectivity : Primrec typeCode := by
  have step : Primrec₂ (fun (_ : Nat) (old : Nat) => codecPair old old + 1) := by
    have squarePair : Primrec (fun p : Nat × Nat => codecPair p.2 p.2) :=
      pairPrimitive.comp Primrec.snd Primrec.snd
    exact (Primrec.succ.comp squarePair).to₂
  exact Primrec.nat_rec₁ 1 step

#print axioms pairPrimitive
#print axioms nativeTowerTypeCodeEffectivity

end LogicLineages.PersistentMarking.NativeTowerTypeCodeProof
