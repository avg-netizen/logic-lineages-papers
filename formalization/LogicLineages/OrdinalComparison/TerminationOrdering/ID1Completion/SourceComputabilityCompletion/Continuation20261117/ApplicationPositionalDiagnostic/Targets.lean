module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.Targets
open NumberedLeastCodeRepresentative NumberedMultisetNumeric
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Both entire roots satisfy the literal original syntactic Code guard. -/
def NativeCodeGuards : Prop :=
  evaluate (Continuation20261115.OriginalCodeValidityGuard.check 0)
    (List.Vector.ofFn ![codeNumber left]) = 1 ∧
  evaluate (Continuation20261115.OriginalCodeValidityGuard.check 0)
    (List.Vector.ofFn ![codeNumber right]) = 1
/-- Actual original four-conjunct headMove, not a replacement permutation predicate. -/
def NativeHeadMove : Prop :=
  evaluate (Continuation20261114.OriginalHeadMove.headMove 0 arity)
    (List.Vector.ofFn ![headNumber head, codeNumber base, headNumber head,
      codeNumber target, numbersNumber [], numbersNumber (window.map typeNumber)]) = 1
/-- Original result AST on each (identical) head returns the packed ground result. -/
def NativeResultEquality : Prop :=
  evaluate Continuation20261114.OriginalHeadResult.headResult
    (List.Vector.ofFn ![headNumber head]) = typeNumber ground
/-- Source-only term acceptance, with original raw+1 fuel and empty Gamma. -/
def NativeSourceSuccess : Prop := evaluate checker (input left) = 1
/-- Destination rejection by the same original term checker. -/
def NativeTargetFailure : Prop := evaluate checker (input right) = 0
/-- Concrete diagnostic against raw source-to-target preservation, NOT the typed
neighborhood theorem. No target typing premise, outer G, or installed Context claim. -/
def NativeDiagnostic : Prop := NativeCodeGuards ∧ NativeHeadMove ∧
  NativeResultEquality ∧ NativeSourceSuccess ∧ NativeTargetFailure
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.ApplicationPositionalDiagnostic.Targets
