module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedPrefixWorkingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitWorkingTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Explicit proof-side consumer for execution starting at the protected
suffix itself. The source-root application must discharge this from literal
return geometry; it is not a result-stack invariant. -/
def Consumer (R : Program 2) (body : Positive (Fin 1)) {alpha : Type}
 (Delta : List (Formula alpha)) (suffix output : OTerm alpha) (psi : Formula alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count input results : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing input (suffix.relabel j) results)) →
   Nonempty (Derivation body Theta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) (output.relabel j) count input)) →
   Nonempty (Derivation body Theta (OriginalHereditaryPotentialCompletion.Empty (output.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))
/-- Every actually completed run from a genuine admissible agenda executes its
protected suffix. Counts, front, states and results stay symbolic inside PA
induction. The public source-root projection discharges the suffix consumer. -/
def ActualExit : Prop := ∀ (R : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (c B suffix output count input work results front : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Agenda H M W c B work)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append work front suffix)) →
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input)) →
 Nonempty (Derivation body Delta (OriginalHereditaryPotentialCompletion.Empty output)) →
 Consumer R body Delta suffix output psi → Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitWorkingTargets
