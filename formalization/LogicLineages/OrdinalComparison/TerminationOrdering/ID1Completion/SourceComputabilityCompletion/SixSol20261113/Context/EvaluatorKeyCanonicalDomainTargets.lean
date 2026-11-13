module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- The actual original C at the explicitly NEW tuple preserves original
source/target/window admission. Output admission, a type witness, calibration,
and E-preservation are not premises; this does not claim E-preservation. -/
def ActualCanonicalDomain : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input out parameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W input parameter)) →
 Nonempty (Derivation body Delta (graph2 (C p H G W P) out input parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W out parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalDomainTargets
