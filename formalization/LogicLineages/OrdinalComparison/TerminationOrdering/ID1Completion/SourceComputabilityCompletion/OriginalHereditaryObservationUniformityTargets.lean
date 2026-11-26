module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationUniformityTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedWindowEquivalence
/-- Native class uniformity in EVERY typed context for the fixed original window.
No arbitrary-R existence or internal graph law is asserted. -/
def Uniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) : Prop :=
  ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
    WindowPrimary (Fin n) arity symbols S Gamma q r →
    evaluate Q (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
    evaluate Q (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])
def RootPreserves : Prop := ∀ Q n arity symbols S c,
  Uniform Q n arity symbols S c →
  Uniform (OriginalRootObservation.rootObservation Q) n arity symbols S c
def RowsPreserves : Prop := ∀ Q n arity symbols S c,
  Uniform Q n arity symbols S c →
  Uniform (OriginalHereditaryDeletionRows.rows Q) n arity symbols S c
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationUniformityTargets
