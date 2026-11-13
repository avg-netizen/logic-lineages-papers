module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion EvaluatorKeyPut EvaluatorKeyCanonicalInductionDefinitions
open EvaluatorKeyCanonicalPreservationDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- CONDITIONAL forward preservation by actual C at the explicitly NEW tuple.
The uniform retained-R rule is explicit; it has not been proved for arbitrary
packages. Only input Domain and actual C computation are internal premises.
Output Domain, constructor fields and child semantics must be derived. This
is neither unconditional E preservation nor Object cancellation. -/
def ActualConditionalPreservation : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
 Compatible p H G W →
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input out parameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W input parameter)) →
 Nonempty (Derivation body Delta (graph2 (C p H G W P) out input parameter)) →
 Nonempty (Derivation body Delta
   (Domain p H G W out parameter ⊓ Same p H G W input out parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationTargets
