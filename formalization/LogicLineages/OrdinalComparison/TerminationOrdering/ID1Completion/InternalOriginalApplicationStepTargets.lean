module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalApplicationStep

/-- Genuine internal acceptance transport for the exact outer-guarded
normalized checker. The old validity, membership and step leaves are arbitrary
Program ASTs; no external calibration, truth reflection, successful decode,
semantic typing or assumed application-closure theorem is a premise.
The actual recursive validity closure must discharge the new outer guard. -/
def ActualOriginalGuardedApplicationStep : Prop :=
  ∀ (body : Positive (Fin 1)) (data : Data) (α : Type)
    (arrow d e s t a k sourceApp targetApp liftedStep : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((liftPremises data arrow d e s t a k sourceApp targetApp liftedStep ⊓
      accepted data s t k).imp
      (accepted data sourceApp targetApp liftedStep)))

/-- ONE shared leaf selection precedes every positive body, variable type,
symbolic type code, endpoint and certificate. Its constructed recursive
validity, endpoint and guarded step are all calibrated on EVERY natural input
to the unchanged original functions, for arbitrary S and fixed Gamma.
The internal rule applies to this SAME literal selected AST. No subtype-window
closure, representative congruence, joint-Gamma uniformity or path wrapper is
asserted. This is a supporting source function-side application-step rule. -/
def ActualOriginalSelectedApplicationStep : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  ∃ data : Data,
    Calibrated n arity symbols S Gamma table data ∧
      (SelectedCalibrated n arity symbols S Gamma table data ∧
        ∀ (body : Positive (Fin 1)) (α : Type)
          (arrow d e s t a k sourceApp targetApp liftedStep : OrdinaryArithmetic.Term α),
        Nonempty (Derivation body []
          ((liftPremises data arrow d e s t a k sourceApp targetApp liftedStep ⊓
            accepted data s t k).imp
            (accepted data sourceApp targetApp liftedStep))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationStepTargets
