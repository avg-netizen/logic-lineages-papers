module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseDefinitions
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
 (oldS oldT rootCert rootParam codomain erasedType cutoff context before after : OTerm alpha) : Prop :=
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
 Nonempty (Derivation body Theta (OriginalLambdaOriginalRankDefinitions.Result leaf childS childT childParam
   oldChildS oldChildT (before.relabel j) (after.relabel j)))

/-- Actual raw-final-leaf lambda/nonbottom constructor case. No transformed
Frame, target geometry, child source validity, or desired transport law is a
premise. The explicit local child IH is restricted by actual child selectors, ambient-context inclusion, and a direct object-level Result. This
is NOT the outer application-normalized stepAccepted checker or all RawStep. -/
def ActualContextLambdaErasureCase : Prop :=
 ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
   (endpoint : Program 6) (window : Program 1)
   (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (oldS oldT oldCert oldParam newS newT newParam oldBody domain codomain arrow
     erasedType cutoff gamma extended context before after : OTerm alpha),
 let source := OriginalUniverseDecoder.source H G M W
 let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
   (OriginalTransparentLambdaStep.refined source oldStep)
 Nonempty (Derivation body Delta
   (OriginalLambdaConstructor.Fields oldS domain codomain oldBody arrow)) →
 Nonempty (Derivation body Delta (graph2 source (numeral 1) oldS oldParam)) →
 Nonempty (Derivation body Delta
   (graph4 leaf (numeral 1) oldS oldT oldCert oldParam ⊓
    OriginalHereditaryLambda.LambdaNonbottom oldS oldT oldCert oldParam)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)) →
 Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)) →
 Nonempty (Derivation body Delta
   (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)) →
 ContextChildIH body Delta leaf source oldS oldT oldCert oldParam codomain erasedType cutoff context before after →
 Nonempty (Derivation body Delta
   (OriginalLambdaOriginalRankDefinitions.Result leaf newS newT newParam oldS oldT before after))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureContextCaseDefinitions
