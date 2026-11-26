module

public import LogicLineages.NativeModule.PersistentMarking.ExternalOrdinalInterfaceTargets
public import LogicLineages.NativeModule.PersistentMarking.ExternalOrdinalInterfaceID1Targets
public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperBridgeTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWellFoundedTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticAllContextTargets

/-! Conditional `thm:upper` (Opus B, round 4; not a twin).

Printed (ordinals.tex 315–318): "The confined strict relation is well founded, and
rk_⊐(s) < BH for every ordinary term s."  Comparator `UpperStatement BH` =
`ConfinedStrictWellFounded ∧ UpperBound BH` (the latter is Opus A's shared interface def).

Hypotheses, as named Props over the abstract ordinal `BH`:
- E4 `ExternalOrdinalInterfaceID1Targets.NormTheorem BH` (Pohlers), Opus A's form, used verbatim;
- R1 `IndividualAccessibility` below: the printed form of the input the proof uses — "the
  arithmetic accessibility proof supplies an ID₁ proof of the individual I-membership of tr(s)
  in this fixed window" — i.e. for each closed window some correct arithmetization of the
  four checkers and some outer context at which every admitted scalar address has an
  ID₁-derivable I-atom.  Opus A's `InternalAccessibility d c` (the uniform all-terms sentence)
  is the stronger uniform form; passing from it to the individual atoms needs internal
  ∀-elimination, internal Σ₁-truth of the scalar checker graph at the address numeral and the
  closed-term identity `tagTerm false (numeral x) = numeral (2x)`, which are not in the
  repository as lemmas, so that bridge is not claimed here. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.SourcePresentation
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowExternalIDOperators NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticAllContextTargets (AdmittedAddress)

/-- R1 (individual form). -/
def IndividualAccessibility : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (i j : Program 1) (r d : Program 3) (c : Nat),
      Evaluates (checks S.entries (fixed S K)) i j r d ∧
      ∀ x, AdmittedAddress S K x →
        Nonempty (Derivation (sourceBody (data i j r d) c) []
          (Positive.predicate (α := Empty) (numeral (tagScalar x))).formula)

/-- The printed statement of `thm:upper` with the abstract ordinal `BH`. -/
def UpperStatement (BH : Ordinal.{0}) : Prop :=
  NumberedWindowExternalWellFoundedTargets.ConfinedStrictWellFounded ∧
    ExternalOrdinalInterfaceTargets.UpperBound BH

/-- Conditional `thm:upper`: from E4 and R1. -/
def ConditionalUpper : Prop :=
  ∀ BH : Ordinal.{0}, ExternalOrdinalInterfaceID1Targets.NormTheorem BH → IndividualAccessibility →
    UpperStatement BH

end LogicLineages.PersistentMarking.ConditionalUpperTargets
