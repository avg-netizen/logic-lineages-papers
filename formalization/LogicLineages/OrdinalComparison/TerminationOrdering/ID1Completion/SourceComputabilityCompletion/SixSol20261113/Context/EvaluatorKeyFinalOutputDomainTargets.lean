module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalFoldDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion EvaluatorKeyPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual final application-fold output admission at the explicitly NEW tuple.
No output source, target, type, window, or E preservation premise. -/
def ActualFinalFoldDomain : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input out parameter : OTerm alpha),
 Nonempty (Derivation body Delta (Domain p H G W input parameter)) →
 Nonempty (Derivation body Delta
   (graph2 (EvaluatorKeyFinalFoldDefinitions.fold p H G W P) out input parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W out parameter))
/-- Expose the actual Object output's raw domain and retained Gamma. All
coordinates refer to original pairs/selectors and the SAME final tuple.
This is output admission, not E preservation or erase/shift cancellation. -/
def ActualObjectDomain : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (context inputObject outputObject gamma raw outRaw parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inputObject gamma raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
 Nonempty (Derivation body Delta (Domain p H G W raw parameter)) →
 Nonempty (Derivation body Delta
   (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) outputObject context inputObject)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right outRaw outputObject)) →
 Nonempty (Derivation body Delta
   (Domain p H G W outRaw parameter ⊓ graph2 InternalPairing.pairing outputObject gamma outRaw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyFinalOutputDomainTargets
