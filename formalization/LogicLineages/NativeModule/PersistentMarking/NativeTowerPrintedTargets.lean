module

public import LogicLineages.NativeModule.PersistentMarking.NativeTowerTargets
public import LogicLineages.NativeModule.PersistentMarking.NativeOrdinalExponentialTargets
public import LogicLineages.PersistentMarking.OrdinalOmegaOrbitTargets

@[expose] public section

/-! The printed instance of the towers: `fix` is the printed native `fix = λf z. It w f (s z)`
(`NativeOrdinalExponentialTargets.ordinalFix`), and `Fix` is its semantic value, characterized by
the arithmetic and omega equations of ordinals.tex 498–530 (`fix f z = f^ω(z+1)` by (I)). -/

namespace LogicLineages.PersistentMarking.NativeTowerPrintedTargets
open NativeIteratorStrictTargets NativeIndexedCarrierTargets
open OrdinalRealizationTargets NativeOrdinalRealizationTargets
open OrdinalArithmeticOrbitTargets OrdinalOmegaOrbitTargets NativeTowerTargets

def PrintedTowerRealization : Prop :=
  ∀ S, ∃ wf : WellFounded (@NativeBelow S indexType),
    ∀ (Z : CountableOrdinal) (s : CountableOrdinal → CountableOrdinal)
      (add mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
      (w one : CountableOrdinal) (pow : CountableOrdinal → CountableOrdinal)
      (fix : (CountableOrdinal → CountableOrdinal) → CountableOrdinal → CountableOrdinal),
      OrdinalArithmeticEquations Z s add mul → OmegaArithmeticEquations Z s mul w one pow fix →
      ∀ l, ∃ t : (nativeTerms S).term (tier (l+2)),
        t.val = towerTerm NativeOrdinalExponentialTargets.ordinalFix l ∧
        Realizes (nativeTerms S) wf (tier (l+2)) t (towerValue (fix : Value (tier 2)) l)

end LogicLineages.PersistentMarking.NativeTowerPrintedTargets
