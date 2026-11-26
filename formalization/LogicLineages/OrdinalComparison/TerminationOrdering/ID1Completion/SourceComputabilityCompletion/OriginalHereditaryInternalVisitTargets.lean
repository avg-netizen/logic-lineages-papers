module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryCombinedStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- CPS construction of a genuine runtime visit. Only original state geometry
and actual expansion are inputs. All administrative rows and output are queried
from total original Programs; no desired transition is supplied. -/
def VisitCases : Prop := ∀ (R : Program 2) (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input work results visit rest parent jobs : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input work results)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work visit rest)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit (numeral 0) parent)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)) →
 (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (childCount deletionCount counts payload returnFrame tagged returnRest next out : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 (OriginalRawSyntaxTransport.arityOf OriginalHereditaryAnnotatedVisit.raw) childCount (input.relabel j))) →
   Nonempty (Derivation body Theta (graph1 (.composition OriginalContextInsertion.length (fun _ : Fin 1 => rightOf OriginalHereditaryAnnotatedVisit.parameter)) deletionCount (input.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing counts childCount deletionCount)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing payload (parent.relabel j) counts)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)) →
   Nonempty (Derivation body Theta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged (jobs.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode returnRest returnFrame (rest.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append next tagged returnRest)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing out next (results.relabel j))) →
   Nonempty (Derivation body Theta (graph1 (OriginalHereditaryCombinedStep.step R) out (input.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalVisitTargets
