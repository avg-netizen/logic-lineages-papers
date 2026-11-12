module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCaseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureFinalCaseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaErasureCaseDefinitions

/-- The local ranked lambda erasure case at the literal actual DirectBottomGlobal final leaf.
The explicit child IH remains required; this is not all-RawStep transport. -/
def ActualOriginalLambdaErasureFinalCase : Prop :=
 ∀ (p : UniformCertificateCompletion.GlobalSourcePackage.Inputs)
   (H G : Program 1) (W : Program 2) (P : Program 3)
   (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
   (oldS oldT oldCert oldParam newS newT newParam oldBody domain codomain arrow
     erasedType cutoff gamma extended context before after : OTerm alpha),
 let source := OriginalTransparentDirectBottomGlobal.source p H G W
 let leaf := (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep
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
 ChildIH body leaf source oldS oldT codomain erasedType cutoff context before after →
 Nonempty (Derivation body Delta
   (OriginalLambdaOriginalRankDefinitions.Result leaf newS newT newParam oldS oldT before after))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureFinalCaseTargets
