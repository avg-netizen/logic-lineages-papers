module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedDirectBottomDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- A local, binder-stable induction supplier ONLY for the actual bodies of
these two original parents. It consumes real old source acceptance, the SAME
leaf's accepted old certificate, and both exact erase/Insert/context graphs.
The cutoff is the parent's successor. It is an explicit IH, not a proved
unconditional erasure or canonical-coherence assertion. -/
def ContextChildIH {alpha : Type} (body : Positive (Fin 1)) (Delta : List (Formula alpha))
 (leaf : Program 4) (source : Program 2)
 (oldS oldT rootCert rootParam codomain erasedType cutoff context : OTerm alpha) : Prop :=
 ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
 (∀ f ∈ Delta, f.relabel j ∈ Theta) →
 ∀ (oldChildS oldChildT oldCert oldParam childS childT childParam gamma extended : OTerm beta),
 Nonempty (Derivation body Theta
   (graph2 OriginalLambdaConstructor.bodyCode oldChildS (codomain.relabel j) (oldS.relabel j))) →
 Nonempty (Derivation body Theta
   (graph2 OriginalLambdaConstructor.bodyCode oldChildT (codomain.relabel j) (oldT.relabel j))) →
 Nonempty (Derivation body Theta (graph2 source (numeral 1) oldChildS oldParam)) →
 Nonempty (Derivation body Theta (graph4 leaf (numeral 1) oldChildS oldChildT oldCert oldParam)) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing oldParam (context.relabel j) extended)) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParam (context.relabel j) gamma)) →
 Nonempty (Derivation body Theta
   (OriginalContextInsertion.Insert (erasedType.relabel j) (suc (cutoff.relabel j)) gamma extended)) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw
   childS (erasedType.relabel j) (suc (cutoff.relabel j)) oldChildS)) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw
   childT (erasedType.relabel j) (suc (cutoff.relabel j)) oldChildT)) →
 Nonempty (Derivation body Theta (graph1 OriginalLambdaGuardLeaf.stripCertificate oldCert (rootCert.relabel j))) →
 Nonempty (Derivation body Theta (graph4 OriginalLambdaGuardLeaf.childParameter oldParam
   (oldS.relabel j) (oldT.relabel j) (rootCert.relabel j) (rootParam.relabel j))) →
 Nonempty (Derivation body Theta (OriginalExistentialRankResultDefinitions.Result leaf childS childT childParam
   oldChildS oldChildT))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureDefinitions
