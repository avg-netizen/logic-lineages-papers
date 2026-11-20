module

public import LogicLineages.PersistentMarking.OrdinalNativeOrbitProof

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalArithmeticOrbitTargets
open OrdinalRealizationTargets OrdinalNativeOrbitProof

def OrdinalArithmeticEquations (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal) : Prop :=
  Z.val = 0 ∧
  (∀ a, (s a).val = a.val + 1) ∧
  (∀ a b, add a b = orbit .base s a b ∧ (add a b).val = a.val + b.val) ∧
  (∀ a b, mul a b = orbit .base (fun x => add x a) Z b ∧ (mul a b).val = a.val * b.val)

def ExactOrdinalArithmeticOrbits : Prop :=
  ∃ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul

end LogicLineages.PersistentMarking.OrdinalArithmeticOrbitTargets
