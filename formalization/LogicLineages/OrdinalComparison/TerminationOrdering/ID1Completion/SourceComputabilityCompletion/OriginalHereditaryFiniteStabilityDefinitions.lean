module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStability
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryNativeBoundDefinitions
def value (Q : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat) (s : State (Fin n) arity) : Nat :=
 evaluate Q (List.Vector.ofFn ![packedNumber s.term,Nat.pair c (typesNumber s.context)])
/-- Semantic term children and actual typed context deletions, not scheduler
administrative visits or untyped/malformed raw states. -/
def StepAgreement (Q T : Program 2) {n : Nat} {arity : Fin n → Nat} (c : Nat) (s : State (Fin n) arity) : Prop :=
 ∀ t, Step s t → value Q c t = value T c t
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStability
