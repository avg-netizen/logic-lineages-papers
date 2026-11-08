module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalResultFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFold
open Source
open InternalOriginalUniformParameterLeaves (parameterCode)
open InternalParameterizedCanonicalResultFold (Data foldN goodRunH)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- All-input external calibration of the ACTUAL parameterized bounded
fold and its whole-final-state checker. The value may be malformed, outside
the source universe, or zero. The original raw-application combine, original
packed-target representative, and original parameter codec are unchanged. -/
def FoldCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  ∀ value : Nat,
    evaluate (foldN data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) =
      InternalQuotientEdgeChecker.targetRepresentativeValue n arity symbols S Gamma value ∧
    evaluate (goodRunH data) (List.Vector.ofFn ![value,parameterCode symbols S Gamma table]) = 1

/-- Preserve the same globally selected four binary leaves, their actual
recursive validity and ternary typed checker, and add calibration of their
literal canonical fold. No new leaf, parameter-specialized AST, decoder,
internal reflection rule, or target-universe restriction is introduced. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (data : Data) : Prop :=
  InternalOriginalUniformDescentSelection.SelectedCalibrated
    n arity symbols S Gamma table data ∧
  FoldCalibrated n arity symbols S Gamma table data

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformCanonicalResultFold
