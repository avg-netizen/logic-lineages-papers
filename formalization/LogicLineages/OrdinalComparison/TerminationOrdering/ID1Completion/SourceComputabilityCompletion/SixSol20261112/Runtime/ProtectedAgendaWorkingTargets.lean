module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaWorkingTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Internal associativity for the actual numeric append Program on every raw
list code. The actual relational outputs are retained, without native decoding. -/
def AppendReassociation : Prop := ∀ (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha)) (a b c ab bc out : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append ab a b)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append bc b c)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out ab c)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out a bc))
/-- A genuine visit preserves an arbitrary protected agenda suffix and the
entire actual result stack. Its new front is constructed, not assumed. The
literal new return frame retains the original parent and actual numeric counts. -/
def ProtectedVisitCases : Prop := ∀ (R : Program 2) (body : Positive (Fin 1))
 (alpha : Type) (Delta : List (Formula alpha))
 (input work results visit rest parent jobs front suffix : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)) →
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append rest front suffix)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (counts payload returnFrame newPrefix newWork out : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing payload (parent.relabel j) counts)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append newWork newPrefix (suffix.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing out newWork (results.relabel j))) →
   Nonempty (Derivation body Theta (graph1 (OriginalHereditaryCombinedStep.step R) out (input.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ProtectedAgendaWorkingTargets
