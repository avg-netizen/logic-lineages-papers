module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceApplicationFieldsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedTraceDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Scoped internal induction supplier only at the literal old application-function child tuple/certificate/parameter. All erasures and context relations are actual graphs. -/
def ChildIH {alpha : Type} (body : Positive (Fin 1)) (Delta : List (Formula alpha))
 (leaf outLeaf : Program 4) (source : Program 2)
 (oldChildS oldChildT oldChildCert oldParam erasedType cutoff context : OTerm alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 ∀ (childS childT newParam gamma extended : OTerm beta),
 Nonempty (Derivation body Theta (graph2 source (numeral 1) (oldChildS.relabel j) (oldParam.relabel j))) →
 Nonempty (Derivation body Theta (graph4 leaf (numeral 1) (oldChildS.relabel j) (oldChildT.relabel j) (oldChildCert.relabel j) (oldParam.relabel j))) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (oldParam.relabel j) (context.relabel j) extended)) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing newParam (context.relabel j) gamma)) →
 Nonempty (Derivation body Theta (OriginalContextInsertion.Insert (erasedType.relabel j) (cutoff.relabel j) gamma extended)) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childS (erasedType.relabel j) (cutoff.relabel j) (oldChildS.relabel j))) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childT (erasedType.relabel j) (cutoff.relabel j) (oldChildT.relabel j))) →
 Nonempty (Derivation body Theta (OriginalExistentialRankResultDefinitions.Result outLeaf childS childT newParam (oldChildS.relabel j) (oldChildT.relabel j)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedClosedApplicationErasureDefinitions
