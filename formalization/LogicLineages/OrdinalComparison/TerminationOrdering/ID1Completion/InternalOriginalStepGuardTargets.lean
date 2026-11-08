module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalOriginalStepGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- One pair of actual validity Programs per fixed original signature, window
and Gamma. Calibration includes every natural input and every window. -/
def ActualOriginalValidityProgramsExist : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
  ∃ data : Data, Calibrated n arity symbols S Gamma data

/-- The literal guard wrapper preserves the entire original zero/one output
on ALL raw triples. Source and target decoding failures, unequal types and
malformed certificates remain rejected. No window-closure premise is added. -/
def ActualOriginalGuardedStepCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : Data) (oldChecker : Program 3),
  Calibrated n arity symbols S Gamma data →
  InternalApplicationStepChecker.StepCalibrated n arity symbols S Gamma table oldChecker →
  ∀ v : List.Vector Nat 3,
    evaluate (checker data oldChecker) v =
      (NumberedNumericStep.numericStepTest n arity symbols S Gamma table
        (v.get 0) (v.get 1) (v.get 2)).toNat

/-- Internal decomposition and reconstruction for arbitrary Program leaves.
The two actual tag outputs are supplied independently; their equality, both
validity graphs and the old checker's output-one graph are exactly acceptance.
No semantic calibration or truth-to-derivability premise occurs. -/
def ActualOriginalAcceptanceAtTags : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldChecker : Program 3)
    (α : Type) (sourceTag targetTag s t k : OTerm α),
  Nonempty (Derivation body []
    ((tagGraphs sourceTag targetTag s t).imp
      ((accepted data oldChecker s t k).iff
        (requirements data oldChecker sourceTag targetTag s t k))))

/-- A source outer-tag graph and accepted original guard-wrapped step derive
the TARGET outer-tag graph at the same symbolic tag, both original validity
graphs and the old acceptance graph. The converse also holds. No target tag
witness is supplied, and calibration is not used as an internal rule. -/
def ActualOriginalTaggedAcceptance : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (oldChecker : Program 3)
    (α : Type) (tag s t k : OTerm α),
  Nonempty (Derivation body []
    ((graph1 InternalUnpair.left tag s).imp
      ((accepted data oldChecker s t k).iff
        (taggedRequirements data oldChecker tag s t k))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalStepGuardTargets
