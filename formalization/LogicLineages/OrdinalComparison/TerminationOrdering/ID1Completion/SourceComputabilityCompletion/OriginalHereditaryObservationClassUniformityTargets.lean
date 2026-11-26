module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationSourceUniformityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationClassUniformityTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedFiniteUniverse
open OriginalHereditaryObservationSourceUniformityTargets
/-- Universal same-key pairs on the original source domain, not a chosen BASE matching. -/
def SameKey : Prop := ∀ Q n arity symbols S c,
  SubtypeClosed (fun t => t ∈ S) → SourceUniform Q n arity symbols S c →
  ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → InUniverse symbols S r.2 →
  representativeCode symbols S q = representativeCode symbols S r →
  evaluate Q (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
  evaluate Q (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])
/-- Same consequence from equality of the actual calibrated representative outputs. -/
def ActualSameKey : Prop := ∀ Q n arity (data : InternalOriginalUniformDescentSelection.Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (c : Nat) (ctx : OrdinaryArithmeticQuotient.Context n),
  Encodable.decode c = some ctx → SubtypeClosed (fun t => t ∈ ctx.1.2) →
  SourceUniform Q n arity ctx.1.1 ctx.1.2 c →
  ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  InUniverse ctx.1.1 ctx.1.2 q.2 → InUniverse ctx.1.1 ctx.1.2 r.2 →
  evaluate data.oldRepresentative (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
    evaluate data.oldRepresentative (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)]) →
  evaluate Q (List.Vector.ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]) =
    evaluate Q (List.Vector.ofFn ![packedNumber r,Nat.pair c (typesNumber Gamma)])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationClassUniformityTargets
