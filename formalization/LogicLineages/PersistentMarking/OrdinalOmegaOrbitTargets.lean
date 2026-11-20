module

public import LogicLineages.PersistentMarking.OrdinalArithmeticOrbitTargets
public import Mathlib.SetTheory.Ordinal.Exponential

@[expose] public section

namespace LogicLineages.PersistentMarking.OrdinalOmegaOrbitTargets
open OrdinalRealizationTargets OrdinalNativeOrbitProof OrdinalArithmeticOrbitTargets
open scoped Ordinal

def OmegaArithmeticEquations (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (mul : CountableOrdinal → CountableOrdinal → CountableOrdinal) (w one : CountableOrdinal)
    (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal) : Prop :=
  w.val = ω ∧ one = s Z ∧ one.val = 1 ∧
  (∀ a, pow a = orbit .base (fun x => mul x w) one a ∧ (pow a).val = (ω : Ordinal.{0}) ^ a.val) ∧
  (∀ f z, fix f z = orbit .base f (s z) w)

def NextIsLeastEpsilon (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal) : Prop :=
  ∀ z, IsLeast {e : Ordinal.{0} | z.val < e ∧ (ω : Ordinal.{0}) ^ e = e} (fix pow z).val

def ExactOrdinalOmegaOrbits : Prop :=
  ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul →
      ∃ (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
        (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
        OmegaArithmeticEquations Z s mul w one pow fix ∧ NextIsLeastEpsilon pow fix

def ExactOrdinalArithmeticThroughNext : Prop :=
  ∃ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
    (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
    (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
    OrdinalArithmeticEquations Z s add mul ∧
    OmegaArithmeticEquations Z s mul w one pow fix ∧ NextIsLeastEpsilon pow fix

end LogicLineages.PersistentMarking.OrdinalOmegaOrbitTargets
