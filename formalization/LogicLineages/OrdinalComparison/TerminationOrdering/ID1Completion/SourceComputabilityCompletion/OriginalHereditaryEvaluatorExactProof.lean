module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProjectionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationSignatureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationEncodingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryRootSignatureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedMultisetNumeric
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedHereditaryView
open OriginalHereditaryEvaluatorDefinitions OriginalHereditaryFiniteStability
open OriginalHereditaryEvaluatorExactTargets

theorem exactPrimary : ExactPrimary := by
 intro n arity data hc c ctx hctx hS Gamma q r hq hr
 constructor
 · intro he
   have hh := OriginalHereditaryEvaluatorExactProjectionProof.baseRootEquality data.oldRepresentative c q r he
   simp only [value] at hh
   have cal := OriginalRootObservationActualProof.representativeAtTyped n arity data hc c ctx hctx
   rw [OriginalRootObservationSignatureProof.actualSignatureCalibration data.oldRepresentative n arity
     ctx.1.1 ctx.1.2 c cal Gamma q,
     OriginalRootObservationSignatureProof.actualSignatureCalibration data.oldRepresentative n arity
     ctx.1.1 ctx.1.2 c cal Gamma r] at hh
   exact (NumberedHereditaryRootSignatureProof.exactRootSignature n arity ctx.1.1 ctx.1.2 Gamma hS q r hq hr).mp
     (OriginalRootObservationEncodingProof.signatureInjective n hh)
 · intro h
   exact OriginalHereditaryEvaluatorProof.sourcePreserves data.oldRepresentative n arity ctx.1.1 ctx.1.2 c hS
     (OriginalHereditaryObservationSourceRootProof.calibratedRepresentative n arity data hc c ctx hctx hS)
     Gamma q r hq hr h

theorem exactAllFinite : ExactAllFinite := by
 intro n arity data hc c ctx hctx hS Gamma q r hq hr
 rw [exactPrimary n arity data hc c ctx hctx hS Gamma q r hq hr]
 constructor
 · intro h depth
   exact (NumberedHereditaryViewProof.exactFiniteDepth n arity ctx.1.1 ctx.1.2 Gamma hS depth q r hq hr).mpr h
 · intro h
   exact (NumberedHereditaryViewProof.exactFiniteDepth n arity ctx.1.1 ctx.1.2 Gamma hS 0 q r hq hr).mp (h 0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryEvaluatorExactProof
