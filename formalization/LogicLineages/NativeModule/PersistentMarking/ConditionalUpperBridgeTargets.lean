module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowGuardedNormTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticScalarTargets
public import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationTargets
public import LogicLineages.PersistentMarking.NumberedWindowPresentationCheckers

/-! New target (Opus B, round 4; not a twin).  The syntactic positive body of the source
presentation, read as an operator on predicates, and the identification of its ordinal stages
with those of the actual tagged accessibility operator `taggedStep S K`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperBridgeTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.SourcePresentation PositiveArithmeticOperators
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowExternalIDOperators NumberedWindowGuardedNormTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowArithmeticScalarTargets (fixed)

/-- The operator of a positive body with one free object variable: `P ↦ {z | B(P, z)}`. -/
def bodyOperator (B : Positive (Fin 1)) : Operator :=
  fun P z => realize P B.formula ![z]

/-- For every closed window there are checker programs evaluating the original checks such
that, at every outer context, the body's operator is the tagged operator and their ordinal
stages coincide. -/
def BodyStageBridge : Prop :=
  ∀ (S : Spine.Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∃ (i j : Program 1) (r d : Program 3),
      Evaluates (checks S.entries (fixed S K)) i j r d ∧
      ∀ c, bodyOperator (sourceBody (data i j r d) c) = taggedStep S K ∧
        ∀ (a : Ordinal.{0}) n,
          ordinalStage (bodyOperator (sourceBody (data i j r d) c)) a n ↔ ordinalStage (taggedStep S K) a n

end LogicLineages.PersistentMarking.ConditionalUpperBridgeTargets
