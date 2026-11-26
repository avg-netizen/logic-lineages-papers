module

public import LogicLineages.PersistentMarking.OrdinalArithmeticRealizationTargets
public import LogicLineages.PersistentMarking.OrdinalRealizationClosureProof

public section

namespace LogicLineages.PersistentMarking.OrdinalArithmeticRealizationProof
open OrdinalRealizationTargets OrdinalRealizationClosureProof OrdinalNativeOrbitProof
open OrdinalArithmeticRealizationTargets
open scoped Ordinal

theorem exact_ArithmeticRealizationComposition : ArithmeticRealizationComposition := by
  intro terms wf op functionSlot edges iterator
  intro Z s add mul w one pow fix arithmetic omega
  obtain ⟨zeroValue, successorValue, additionValue, multiplicationValue⟩ := arithmetic
  obtain ⟨omegaValue, oneEq, _, powerValue, fixValue⟩ := omega
  have backwards := exact_RealizationStrictBackward terms wf functionSlot Base
  have backwardsTwo {source target : terms.term Base} {v : CountableOrdinal}
      (path : TwoStrictEdges source target) (realizes : Realizes terms wf Base target v) :
      Realizes terms wf Base source v := by
    obtain ⟨middle, first, second⟩ := path
    exact backwards source middle v first (backwards middle target v second realizes)
  have call (β : CountableOrdinal) (b : terms.term Base) (hb : Realizes terms wf Base b β)
      (f : CountableOrdinal → CountableOrdinal) (F : terms.term OrdinalFunction)
      (hF : Realizes terms wf OrdinalFunction F f)
      (a : CountableOrdinal) (A : terms.term Base) (hA : Realizes terms wf Base A a) :
      Realizes terms wf Base (applyIterator op b F A) (orbit Base f a β) :=
    iterator β b hb f F hF a A hA

  have zeroRealizes : Realizes terms wf Base op.zero Z := by
    change Z.val ≤ (wf.apply op.zero).rank
    rw [zeroValue]
    exact bot_le
  have successorRealizes : Realizes terms wf OrdinalFunction op.successor s := by
    intro a A hA
    obtain ⟨middle, first, second⟩ := edges.successor A
    have leftDrop : (wf.apply A).rank < (wf.apply middle).rank :=
      (wf.apply middle).rank_lt_of_rel second
    have rightDrop : (wf.apply middle).rank < (wf.apply (applyUnary op.successor A)).rank :=
      (wf.apply (applyUnary op.successor A)).rank_lt_of_rel first
    change a.val ≤ (wf.apply A).rank at hA
    change (s a).val ≤ (wf.apply (applyUnary op.successor A)).rank
    rw [successorValue]
    exact Order.add_one_le_iff.mpr (hA.trans_lt (leftDrop.trans rightDrop))
  have additionRealizes : Realizes terms wf BinaryOrdinalFunction op.addition add := by
    intro a A hA b B hB
    change Realizes terms wf Base (applyBinary op.addition A B) (add a b)
    rw [(additionValue a b).1]
    exact backwardsTwo (edges.addition A B) (call b B hB s op.successor successorRealizes a A hA)
  have multiplyStepRealizes (a : CountableOrdinal) (A : terms.term Base) (hA : Realizes terms wf Base A a) :
      Realizes terms wf OrdinalFunction (op.multiplicationStep A) (fun x => add x a) := by
    intro x X hX
    exact backwards (applyUnary (op.multiplicationStep A) X) (applyBinary op.addition X A)
      (add x a) (edges.multiplyStep A X) (additionRealizes x X hX a A hA)
  have multiplicationRealizes : Realizes terms wf BinaryOrdinalFunction op.multiplication mul := by
    intro a A hA b B hB
    change Realizes terms wf Base (applyBinary op.multiplication A B) (mul a b)
    rw [(multiplicationValue a b).1]
    exact backwardsTwo (edges.multiplication A B)
      (call b B hB (fun x => add x a) (op.multiplicationStep A) (multiplyStepRealizes a A hA)
        Z op.zero zeroRealizes)

  let natValue : Nat → CountableOrdinal := fun n => Nat.rec Z (fun _ pred => s pred) n
  have natValueExact (n : Nat) : (natValue n).val = (n : Ordinal.{0}) := by
    induction n with
    | zero => exact zeroValue
    | succ n ih =>
      change (s (natValue n)).val = (n.succ : Ordinal.{0})
      rw [successorValue, ih, Nat.cast_succ]
  have natRealizes (n : Nat) : Realizes terms wf Base (finiteSuccessor op n) (natValue n) := by
    induction n with
    | zero => exact zeroRealizes
    | succ n ih => exact successorRealizes (natValue n) (finiteSuccessor op n) ih
  have omegaRealizes : Realizes terms wf Base op.omega w := by
    change w.val ≤ (wf.apply op.omega).rank
    rw [omegaValue, ← Ordinal.iSup_natCast]
    apply Ordinal.iSup_le
    intro n
    have rankN := natRealizes n
    change (natValue n).val ≤ (wf.apply (finiteSuccessor op n)).rank at rankN
    rw [natValueExact n] at rankN
    have rankDrop : (wf.apply (finiteSuccessor op n)).rank < (wf.apply op.omega).rank :=
      (wf.apply op.omega).rank_lt_of_rel (edges.omega n)
    exact rankN.trans rankDrop.le
  have oneRealizes : Realizes terms wf Base (literalOne op) one := by
    rw [oneEq]
    exact successorRealizes Z op.zero zeroRealizes
  have powerStepRealizes : Realizes terms wf OrdinalFunction op.powerStep (fun x => mul x w) := by
    intro x X hX
    exact backwards (applyUnary op.powerStep X) (applyBinary op.multiplication X op.omega)
      (mul x w) (edges.powerStep X) (multiplicationRealizes x X hX w op.omega omegaRealizes)
  have powerRealizes : Realizes terms wf OrdinalFunction op.power pow := by
    intro a A hA
    change Realizes terms wf Base (applyUnary op.power A) (pow a)
    rw [(powerValue a).1]
    exact backwards _ _ _ (edges.power A)
      (call a A hA (fun x => mul x w) op.powerStep powerStepRealizes one (literalOne op) oneRealizes)
  have fixRealizes : Realizes terms wf FixedPointFunction op.fix fix := by
    intro f F hF z T hT
    change Realizes terms wf Base (applyUnary (terms.app OrdinalFunction OrdinalFunction op.fix F) T) (fix f z)
    rw [fixValue f z]
    exact backwardsTwo (edges.fix F T)
      (call w op.omega omegaRealizes f F hF (s z) (applyUnary op.successor T) (successorRealizes z T hT))
  have nextRealizes : Realizes terms wf OrdinalFunction (literalNext op) (fix pow) :=
    fixRealizes pow op.power powerRealizes
  exact ⟨zeroRealizes, successorRealizes, additionRealizes, multiplicationRealizes, omegaRealizes,
    oneRealizes, powerRealizes, fixRealizes, nextRealizes⟩

#print axioms exact_ArithmeticRealizationComposition

end LogicLineages.PersistentMarking.OrdinalArithmeticRealizationProof
