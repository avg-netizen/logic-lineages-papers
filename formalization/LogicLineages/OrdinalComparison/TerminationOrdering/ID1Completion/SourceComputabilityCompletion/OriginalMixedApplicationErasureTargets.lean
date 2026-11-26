module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedApplicationErasureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedApplicationErasureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)
/-- Coordinate-level genuine original application hop. Child/shared-argument erasures are literal graph outputs, not transformed Frame or source oracles. No full path induction/global tuple claim. -/
def ActualAtCoordinates : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow fp ap
  newS newT newChildS newChildT newArg newParam erasedType cutoff gamma extended context : OTerm alpha),
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fp ap oldChildS oldArg oldS)) →
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop (source H G M W)
  oldS oldT oldCert oldParam oldChildS oldChildT oldChildCert oldArg domain codomain arrow)) →
 Nonempty (Derivation body Delta (graph4 (leaf H G M W oldStep) (numeral 1) oldS oldT oldCert oldParam)) →
 Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam context extended)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam context gamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newS erasedType cutoff oldS)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newT erasedType cutoff oldT)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newChildS erasedType cutoff oldChildS)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newChildT erasedType cutoff oldChildT)) →
 Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw newArg erasedType cutoff oldArg)) →
 OriginalMixedApplicationErasureDefinitions.ChildIH body Delta (leaf H G M W oldStep) (source H G M W)
  oldChildS oldChildT oldChildCert oldParam erasedType cutoff context →
 Nonempty (Derivation body Delta (OriginalExistentialRankResultDefinitions.Result (leaf H G M W oldStep) newS newT newParam oldS oldT))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedApplicationErasureTargets
