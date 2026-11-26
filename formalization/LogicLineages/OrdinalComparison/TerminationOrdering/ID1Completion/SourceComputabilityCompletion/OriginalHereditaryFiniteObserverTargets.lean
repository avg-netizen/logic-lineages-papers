module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedWindowEquivalence NumberedFiniteUniverse
open OriginalHereditaryObservationSourceUniformityTargets OriginalHereditaryFiniteObserver
/-- Every finite semantic depth retains source Primary uniformity. -/
def AllDepths : Prop := ∀ R n arity symbols S c,
 SubtypeClosed (fun t => t ∈ S) → SourceUniform R n arity symbols S c →
 ∀ depth, SourceUniform (family R depth) n arity symbols S c
/-- Genuine original old representative supplies the base, not an assumed
uniformity oracle. This is native calibration support only. -/
def CalibratedDepths : Prop := ∀ n arity (data : InternalOriginalUniformDescentSelection.Data),
 InternalOriginalUniformDescentSelection.Calibrated n arity data →
 ∀ (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n), Encodable.decode c = some ctx →
 SubtypeClosed (fun t => t ∈ ctx.1.2) → ∀ depth,
 SourceUniform (family data.oldRepresentative depth) n arity ctx.1.1 ctx.1.2 c
/-- Source class invariance also holds when the finite depth is selected by
actual context length plus twice original structural size. No stabilization or
scheduler calibration follows from this theorem alone. -/
def SelectedDepth : Prop := ∀ R n arity symbols S c,
 SubtypeClosed (fun t => t ∈ S) → SourceUniform R n arity symbols S c →
 ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
 InUniverse symbols S q.2 → InUniverse symbols S r.2 → WindowPrimary (Fin n) arity symbols S Gamma q r →
 evaluate (family R (Gamma.length + 2 * NumberedPrimaryEquivalence.size q.2))
   (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
 evaluate (family R (Gamma.length + 2 * NumberedPrimaryEquivalence.size r.2))
   (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteObserverTargets
