module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformCertificateCompletion

open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof
open OriginalStructuralClassKeyDefinitions OriginalStructuralClassKeyActiveProof
open OriginalTypedDecoderTransportLogicalProof (iffForward)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Both raw lambda ranks are their actual child rank, with no transformed
or canonical rank identification. -/
theorem sharedLambdaRank (input out d e child childOut childRank rank : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (ho : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw childRank child)))
 (hco : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw childRank childOut)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out))) :
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)) := by
 have ri := OriginalFinalGuardedRankConstructorProof.lambdaValue input d e child childRank hi hc
 have ro := OriginalFinalGuardedRankConstructorProof.lambdaValue out d e childOut childRank ho hco
 have he := valueUnique OriginalRawSyntaxTransport.variableRankPackedRaw childRank rank
   (Fin.cons out Fin.elim0) ro hr
 exact outputTransport OriginalRawSyntaxTransport.variableRankPackedRaw childRank rank
   (Fin.cons input Fin.elim0) he ri

/-- All four terms are already erased and decoded. The two parent keys
share one actual deleted parameter; both child keys share its actual extended
child parameter. There is no key comparison across different contexts. -/
theorem lambdaAtErased (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
 (input out d e child childOut childKey childRank keyValue rank parameter childParameter : OTerm alpha)
 (hai : Nonempty (Derivation body Delta (Active p H G W input parameter)))
 (hao : Nonempty (Derivation body Delta (Active p H G W out parameter)))
 (hac : Nonempty (Derivation body Delta (Active p H G W child childParameter)))
 (haco : Nonempty (Derivation body Delta (Active p H G W childOut childParameter)))
 (hfi : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields input d e child parameter childParameter)))
 (hfo : Nonempty (Derivation body Delta (OriginalLambdaTraversalInternal.LambdaFields out d e childOut parameter childParameter)))
 (hi : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor input d e child)))
 (ho : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e childOut)))
 (hkc : Nonempty (Derivation body Delta (graph2 (key p H G W) childKey child childParameter)))
 (hkco : Nonempty (Derivation body Delta (graph2 (key p H G W) childKey childOut childParameter)))
 (hrc : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw childRank child)))
 (hrco : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw childRank childOut)))
 (hk : Nonempty (Derivation body Delta (graph2 (key p H G W) keyValue out parameter)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out))) :
 Nonempty (Derivation body Delta (graph2 (key p H G W) keyValue input parameter)) ∧
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input)) := by
 have law := OriginalStructuralTraversalKeyConstructorProof.lambdaAtCoreValues p H G W
   input out d e child childOut childKey parameter childParameter keyValue hai hao hfi hfo
   (keyToCore p H G W child childKey childParameter hac hkc)
   (keyToCore p H G W childOut childKey childParameter haco hkco)
 exact ⟨iffForward law hk, sharedLambdaRank input out d e child childOut childRank rank hi ho hrc hrco hr⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaCoreProof
