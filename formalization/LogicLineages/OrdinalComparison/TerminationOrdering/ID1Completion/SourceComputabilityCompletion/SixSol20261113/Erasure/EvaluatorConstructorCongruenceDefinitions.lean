module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
/-- EXPLICIT conditional internal admissible rule, uniform in proof context,
variables and parameter. No native calibration is asserted. The quantified
parameter includes every actual deleted and lambda-extended parameter. -/
def UniformRetainedCompatibility (R : Program 2) (H G : Program 1) (M W : Program 2) : Prop :=
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (left right parameter value : OTerm alpha),
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)) →
 Nonempty (Derivation body Delta (graph2 R value left parameter)) →
 Nonempty (Derivation body Delta (graph2 R value right parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceDefinitions
