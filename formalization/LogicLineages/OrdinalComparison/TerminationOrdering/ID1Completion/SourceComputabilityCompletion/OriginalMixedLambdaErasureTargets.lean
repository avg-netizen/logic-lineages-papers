module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)
/-- Typed original lambda-hop adapter at NEW L. The actual recognizer must supply genuine old hop geometry; acceptance alone does not imply it. No transformed Frame or source-validity oracle is a premise. The explicit internal IH is confined to actual stripped children and ambient inclusion. -/
def ActualAtFields : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (oldS oldT oldCert oldParam oldBody oldTargetBody oldChildCert oldChildParam domain codomain arrow context
  gamma extended oldChildExtended newS newT newParam erasedType cutoff : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldS domain codomain oldBody arrow)) →
 Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields oldT domain codomain oldTargetBody arrow)) →
 Nonempty (Derivation body Delta (OriginalTransparentLambdaStep.LambdaHop (source H G M W)
  oldS oldT oldCert oldParam oldBody oldTargetBody oldChildCert oldChildParam domain codomain context extended oldChildExtended)) →
 Nonempty (Derivation body Delta (graph4 (leaf H G M W oldStep) (numeral 1) oldS oldT oldCert oldParam)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)) →
 OriginalMixedLambdaErasureDefinitions.ContextChildIH body Delta (leaf H G M W oldStep) (source H G M W)
  oldS oldT oldCert oldParam codomain erasedType cutoff context →
 Nonempty (Derivation body Delta (OriginalExistentialRankResultDefinitions.Result (leaf H G M W oldStep) newS newT newParam oldS oldT))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLambdaErasureTargets
