module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorFixedPointTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationActualTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedHereditaryView
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
/-- Exact native equivalence for an actual calibrated representative base.
The evaluator is auxiliary: its output is not asserted equal to oldRepresentative. -/
def ExactPrimary : Prop := ∀ n (arity : Fin n → Nat) (data : InternalOriginalUniformDescentSelection.Data),
 InternalOriginalUniformDescentSelection.Calibrated n arity data →
 ∀ c (ctx : OrdinaryArithmeticQuotient.Context n), Encodable.decode c = some ctx →
 SubtypeClosed (fun t => t ∈ ctx.1.2) →
 ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
 InUniverse ctx.1.1 ctx.1.2 q.2 → InUniverse ctx.1.1 ctx.1.2 r.2 →
(value (evaluator data.oldRepresentative) c ⟨Gamma,q⟩ =
   value (evaluator data.oldRepresentative) c ⟨Gamma,r⟩) ↔ WindowPrimary (Fin n) arity ctx.1.1 ctx.1.2 Gamma q r
/-- All finite original HereditaryView depths, under their actual source domain.
No arbitrary-observer collision claim or internal arithmetic reflection. -/
def ExactAllFinite : Prop := ∀ n (arity : Fin n → Nat) (data : InternalOriginalUniformDescentSelection.Data),
 InternalOriginalUniformDescentSelection.Calibrated n arity data →
 ∀ c (ctx : OrdinaryArithmeticQuotient.Context n), Encodable.decode c = some ctx →
 SubtypeClosed (fun t => t ∈ ctx.1.2) →
 ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
 InUniverse ctx.1.1 ctx.1.2 q.2 → InUniverse ctx.1.1 ctx.1.2 r.2 →
(value (evaluator data.oldRepresentative) c ⟨Gamma,q⟩ =
   value (evaluator data.oldRepresentative) c ⟨Gamma,r⟩) ↔ ∀ depth, HereditaryView ctx.1.1 ctx.1.2 depth q r
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactTargets
