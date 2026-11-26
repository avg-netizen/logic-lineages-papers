module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorOtherMarksVariableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open Context.EvaluatorChildrenSharedProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorConstructorCongruenceDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Extract an actual common evaluator graph at any already queried left value.
This does not evaluate native syntax or assume equality of parent outputs. -/
theorem evaluatorValue (R : Program 2) (left right parameter value : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (SameEvaluator R left right parameter)))
 (hl : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value left parameter))) :
 Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) value right parameter)) := by
 apply EvaluatorErasureSyntax.sameCases R left right parameter _ hs
 intro beta j Theta common hj hv
 have hl' := renameInto hl j Theta hj
 simp only [graph2Rename] at hl'
 have he := valueUnique (OriginalHereditaryEvaluatorDefinitions.evaluator R) common (value.relabel j)
   (Fin.cons (left.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andLeft hv) hl'
 have hr := outputTransport (OriginalHereditaryEvaluatorDefinitions.evaluator R) common (value.relabel j)
   (Fin.cons (right.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he (andRight hv)
 simpa only [graph2Rename] using hr
/-- The two independent root payload transfers, explicitly conditional on the
uniform internal retained-R rule. No constructor or deletion rows are claimed. -/
theorem childValues (R : Program 2) (H G : Program 1) (M W : Program 2)
 (compat : UniformRetainedCompatibility R H G M W)
 (left right parameter retained observed : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (hr : Nonempty (Derivation body Delta (graph2 R retained left parameter)))
 (he : Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) observed left parameter))) :
 Nonempty (Derivation body Delta (graph2 R retained right parameter)) ∧
 Nonempty (Derivation body Delta
   (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) observed right parameter)) := by
 exact ⟨compat body alpha Delta left right parameter retained ha hr,
   evaluatorValue R left right parameter observed (andRight (andRight ha)) he⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorValueProof
