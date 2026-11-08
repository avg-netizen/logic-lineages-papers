module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldTargets
open Source InternalOriginalUniformCanonicalResultFold
open InternalParameterizedCanonicalResultFold (Data)

/-- The same globally calibrated tuple feeds the exact raw-application
fold at every original window/Gamma parameter. Original payload induction
and representative congruence must prove all-input identification; neither
canonicality, successful decoding nor an internal reflection is supplied. -/
def ActualOriginalUniformCanonicalResultFoldCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
    InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
    SubtypeClosed (fun tau => tau ∈ S) →
    FoldCalibrated n arity symbols S Gamma table data

/-- One four-leaf tuple is selected after n/arity and BEFORE every window,
Gamma, table, arithmetic body and symbolic parameter. Its existing descent
laws and the literal canonical fold's invariant, typed-output and original
representative/application laws are conclusions, together with all-input
external calibration. This is not an unqualified CertifiedApplicationLift. -/
def ActualOriginalUniformCanonicalResultFoldSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ data : Data,
    InternalOriginalUniformDescentSelection.Calibrated n arity data ∧
    InternalOriginalUniformDescentSelection.InternalLaws data ∧
    InternalParameterizedCanonicalResultFold.InternalLaws data ∧
    ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
      SubtypeClosed (fun tau => tau ∈ S) →
      SelectedCalibrated n arity symbols S Gamma table data

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFoldTargets
