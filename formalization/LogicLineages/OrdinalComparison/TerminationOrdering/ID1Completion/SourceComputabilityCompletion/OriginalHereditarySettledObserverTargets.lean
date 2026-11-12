module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open OriginalHereditaryNativeBoundDefinitions OriginalHereditaryFiniteObserver OriginalHereditaryFiniteStability
open OriginalHereditarySettledObserverDefinitions
/-- Exact recursive layer at a common parent depth; StepNormalization below
replaces every actual child/deletion dependency by its own settled value. -/
def Unfolding : Prop := ∀ R n arity c (s : State (Fin n) arity),
 settledValue R c s = Nat.pair
   (value (OriginalRootObservation.rootObservation R) c s)
   (Nat.pair (value (OriginalRootObservation.rootObservation (family R (weight s))) c s)
     (value (OriginalHereditaryDeletionRows.rows (family R (weight s))) c s))
def StepNormalization : Prop := ∀ R n arity c (s t : State (Fin n) arity),
 Step s t → value (family R (weight s)) c t = settledValue R c t
/-- Original source-class uniformity, not internal graph reflection. -/
def Uniformity : Prop := ∀ R n arity symbols S c,
 SubtypeClosed (fun t => t ∈ S) →
 OriginalHereditaryObservationSourceUniformityTargets.SourceUniform R n arity symbols S c →
 ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
 NumberedFiniteUniverse.InUniverse symbols S q.2 → NumberedFiniteUniverse.InUniverse symbols S r.2 →
 NumberedWindowEquivalence.WindowPrimary (Fin n) arity symbols S Gamma q r →
 settledValue R c ⟨Gamma,q⟩ = settledValue R c ⟨Gamma,r⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditarySettledObserverTargets
