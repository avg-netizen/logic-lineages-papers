module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildContentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Whole actual annotated expansion observed in forward order and reversed
into the produced stack. A uniform actual return supplies the exact role-one
observation at that value. Neither child values nor a desired argument result
is supplied. Q and runtime R remain independent Programs. -/
def ActualArgumentReturnContent : Prop := ∀ (R Q : Program 2) (H : Program 1) (M W : Program 2)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (job typed rawJob raw parameter gamma c children deletions counts payload frame jobs forward produced value : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed (numeral 0) rawJob)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W (numeral 1) (numeral 0) raw gamma c)) →
 Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)) →
 Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)) →
 Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q)) forward jobs)) →
 Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)) →
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R frame produced value)) →
 Nonempty (Derivation body Delta (graph1 (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) value job))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentTargets
