module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def Consumer (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) {alpha : Type} (Delta : List (Formula alpha))
 (c B input suffix : OTerm alpha) (psi : Formula alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (newPrefix nextWork nextResults next : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing next nextWork nextResults)) →
   Nonempty (Derivation body Theta (graph1 (OriginalHereditaryCombinedStep.step R) next (input.relabel j))) →
   Nonempty (Derivation body Theta (OriginalHereditaryInternalAgenda.Agenda H M W (c.relabel j) (B.relabel j) nextWork)) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append nextWork newPrefix (suffix.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))
/-- A live arbitrary prefix executes one actual tick while preserving its
protected agenda suffix. All supported term/list visit and return cases are
covered by actual admissibility. No result-content invariant is supplied and
the new prefix, result stack and state are internally constructed. -/
def ActualStepCases : Prop := ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B input work results prefix head tail suffix : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append work prefix suffix)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode prefix head tail)) →
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Agenda H M W c B work)) →
 Consumer R H M W body Delta c B input suffix psi →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixTargets
