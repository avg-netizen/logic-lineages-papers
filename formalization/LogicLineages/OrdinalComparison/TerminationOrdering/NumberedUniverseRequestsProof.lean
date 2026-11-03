module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedAuxiliaryCoding
open NumberedAuxiliaryDecoding NumberedNumericCarrier NumberedUniverseRequests

theorem termExpansion : NumberedUniverseRequestsTargets.ActualTermExpansion := by
  intro n arity symbols S Gamma tau code
  cases code with
  | var index =>
    have hc := NumberedVariableDecoderPrimrecProof.variableSuccessCalibration Gamma tau index
    cases hv : decodeVariable Gamma tau index with
    | none =>
      have hlookup : ¬ Gamma[index]? = some tau := by
        simpa [hv] using hc.symm
      simp [valid, decodeTerm, hv, expandedValid, NumberedUniverseRequests.guard,
        NumberedTypedRequests.expand, hlookup]
    | some value =>
      have hlookup : Gamma[index]? = some tau := by
        simpa [hv] using hc.symm
      simp [valid, decodeTerm, hv, universeTest, expandedValid, NumberedUniverseRequests.guard,
        NumberedTypedRequests.expand, hlookup]
  | lam sigma body =>
    cases tau with
    | ground =>
      simp [valid, decodeTerm, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
    | arrow domain result =>
      by_cases h : sigma = domain
      · subst sigma
        cases hb : decodeTerm arity (domain :: Gamma) result body <;>
          simp [valid, decodeTerm, hb, universeTest, expandedValid, NumberedUniverseRequests.guard,
            NumberedTypedRequests.expand]
      · simp [valid, decodeTerm, h, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | app sigma q a =>
    cases hq : decodeTerm arity Gamma (.arrow sigma tau) q <;>
      cases ha : decodeTerm arity Gamma sigma a <;>
      simp [valid, decodeTerm, hq, ha, universeTest, expandedValid, NumberedUniverseRequests.guard,
        NumberedTypedRequests.expand, bind, pure, Bool.and_assoc]
  | bottom result =>
    by_cases h : result = tau <;>
      simp [valid, decodeTerm, h, universeTest, expandedValid, NumberedUniverseRequests.guard,
        NumberedTypedRequests.expand]
  | ordinary head base =>
    by_cases h : headResult (decodeHead head) = tau
    · subst tau
      cases hb : decodeArguments arity Gamma (headArguments arity (decodeHead head)) base <;>
        simp [valid, decodeTerm, hb, universeTest, expandedValid, NumberedUniverseRequests.guard,
          NumberedTypedRequests.expand]
    · simp [valid, decodeTerm, h, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | numbered k head result base types extras =>
    by_cases h : result = tau
    · cases hb : decodeArguments arity Gamma (headArguments arity (decodeHead head)) base <;>
        cases he : decodeArguments arity Gamma types extras <;>
        simp [valid, decodeTerm, h, hb, he, universeTest, expandedValid, NumberedUniverseRequests.guard,
          NumberedTypedRequests.expand, bind, pure, Bool.and_assoc]
    · simp [valid, decodeTerm, h, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | argumentsNil =>
    simp [valid, decodeTerm, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | argumentsCons sigma q rest =>
    simp [valid, decodeTerm, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]

theorem argumentsExpansion : NumberedUniverseRequestsTargets.ActualArgumentsExpansion := by
  intro n arity symbols S Gamma types code
  cases code with
  | var index =>
    cases types <;>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | lam sigma body =>
    cases types <;>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | app sigma q a =>
    cases types <;>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | bottom result =>
    cases types <;>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | ordinary head base =>
    cases types <;>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | numbered k head result base extraTypes extras =>
    cases types <;>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
  | argumentsNil =>
    cases types <;>
      simp [valid, decodeArguments, argumentsUniverseTest, expandedValid, NumberedUniverseRequests.guard,
        NumberedTypedRequests.expand]
  | argumentsCons sigma q rest =>
    cases types with
    | nil =>
      simp [valid, decodeArguments, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]
    | cons domain tail =>
      by_cases h : sigma = domain
      · subst sigma
        cases hq : decodeTerm arity Gamma domain q <;>
          cases hr : decodeArguments arity Gamma tail rest <;>
          simp [valid, decodeArguments, hq, hr, argumentsUniverseTest, expandedValid,
            NumberedUniverseRequests.guard, NumberedTypedRequests.expand, bind, pure]
      · simp [valid, decodeArguments, h, expandedValid, NumberedUniverseRequests.guard, NumberedTypedRequests.expand]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseRequestsProof
