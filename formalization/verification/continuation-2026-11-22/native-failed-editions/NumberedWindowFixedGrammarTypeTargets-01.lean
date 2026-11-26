import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets

namespace LogicLineages.PersistentMarking.NumberedWindowFixedGrammarType
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowInternalAuxWindowMemoTargets (typeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalSparsePathEnvelope (run)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)

/-- In the original fixed settings the window's filtered encoded type list
is contained in the unfiltered encoded grammar type list, for every raw code.
This is a metatheoretic fact about the original list constants. -/
def ExactFixedGrammarTypeInclusion : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (n : Nat),
    n ∈ (fixed S K).window.1 → n ∈ (fixed S K).types

/-- A successful numerical output of the calibrated physical guard implies
membership in the grammar type list of those same settings. This does not
assert an open object-derivation rule for extensionally calibrated programs. -/
def ExactFixedGuardRunGrammarType : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty) (T : Program 1),
    TypeGuardCalibrated (fixed S K) T →
      ∀ n, run T n = 1 → n ∈ (fixed S K).types

end LogicLineages.PersistentMarking.NumberedWindowFixedGrammarType
