module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationUniformityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceUniformityTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative
open NumberedWindowEquivalence NumberedFiniteUniverse
/-- Only original source-universe terms, in every actual typed context. -/
def SourceUniform (Q : Program 2) (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty) (c : Nat) : Prop :=
  ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    WindowPrimary (Fin n) arity symbols S Gamma q r →
    evaluate Q (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
    evaluate Q (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])
def RootPreserves : Prop := ∀ Q n arity symbols S c,
  SubtypeClosed (fun t => t ∈ S) → SourceUniform Q n arity symbols S c →
  SourceUniform (OriginalRootObservation.rootObservation Q) n arity symbols S c
def RowsPreserves : Prop := ∀ Q n arity symbols S c,
  SubtypeClosed (fun t => t ∈ S) → SourceUniform Q n arity symbols S c →
  SourceUniform (OriginalHereditaryDeletionRows.rows Q) n arity symbols S c
/-- Native actual old representative in the original decoded closed context.
No assumed observer uniformity and no claim outside its source universe. -/
def CalibratedRepresentative : Prop := ∀ n arity (data : InternalOriginalUniformDescentSelection.Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode c = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  SourceUniform data.oldRepresentative n arity ctx.1.1 ctx.1.2 c
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceUniformityTargets
