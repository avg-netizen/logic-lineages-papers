module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionExistenceLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalOtherTagProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversal OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalLambdaTraversalInternalCompletion OriginalLambdaTraversalInternalCompletionSyntaxProof
open OriginalLambdaTraversalInternalCompletionBindingProof OriginalLambdaTraversalInternalCompletionPayloadBindingProof
open OriginalLambdaTraversalInternalCompletionPayloadSyntaxProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}


open InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open OriginalHereditaryValidityInternalNodeSupportProof (equalityCases weakenProof)

theorem applicationCase (leaf : Program 2) (value parameter payload : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 2) value)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hi : Nonempty (Derivation positive Delta (belowPayload leaf payload))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  let qs : Fin 4 → Program 1 := ![rawDomain,rawType,rawFunction,rawArgument]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons value Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [hasCompletionRename]
  simp only [consTermRename,emptyRename] at hq
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at ht' hp' hi'
  exact OriginalLambdaTraversalInternalCompletionExistenceApplicationProof.fromFields leaf
    (value.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (parameter.relabel j) (payload.relabel j)
    (andIntro ht' (andIntro (hq 0) (andIntro (hq 1) (andIntro (hq 2) (hq 3))))) hp' hi'

theorem lambdaCase (leaf : Program 2) (value parameter payload : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 rawTag (numeral 1) value)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value)))
    (hi : Nonempty (Derivation positive Delta (belowPayload leaf payload))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  let qs : Fin 3 → Program 1 := ![rawDomain,rawCodomain,rawBody]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs (Fin.cons value Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [hasCompletionRename]
  simp only [consTermRename,emptyRename] at hq
  have ht' := renameInto ht j Theta hj
  have hp' := renameInto hp j Theta hj
  have hi' := renameInto hi j Theta hj
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at ht' hp' hi'
  apply programCases childParameter (Fin.cons (value.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) _
  intro gamma k Xi cp hk hc
  rw [hasCompletionRename]
  simp only [consTermRename,emptyRename] at hc
  have ht'' := renameInto ht' k Xi hk
  have hp'' := renameInto hp' k Xi hk
  have hi'' := renameInto hi' k Xi hk
  have hd := renameInto (hq 0) k Xi hk
  have he := renameInto (hq 1) k Xi hk
  have hb := renameInto (hq 2) k Xi hk
  simp only [ApplicationFields,LambdaFields,conjunctionRename,graph1Rename,graph2Rename,SourceComputabilityFormulaSupportProof.numeral,InternalOriginalStepGuard.one,sucRelabel,zRelabel,completesRename,hasCompletionRename,belowPayloadRename,weakBoundRename,InternalApplicationCertifiedResultFoldClosure.payloadFuel,addRelabel] at ht'' hp'' hi'' hd he hb
  exact OriginalLambdaTraversalInternalCompletionExistenceLambdaProof.fromFields leaf
    ((value.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k) ((ys 2).relabel k)
    ((parameter.relabel j).relabel k) cp ((payload.relabel j).relabel k)
    (andIntro ht'' (andIntro hd (andIntro he (andIntro hb hc)))) hp'' hi''

theorem leafCase (leaf : Program 2) (value parameter payload : OTerm alpha)
    (ht : Nonempty (Derivation positive Delta (graph1 otherTag (suc z) value))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply programCases leaf (Fin.cons value (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta produced hj hp
  rw [hasCompletionRename]
  have ht' := renameInto ht j Theta hj
  simp only [graph1Rename,sucRelabel,zRelabel] at ht'
  simp only [consTermRename,emptyRename] at hp
  exact OriginalLambdaTraversalInternalCompletionLeafProof.leafHasCompletion leaf _ _ _ produced ht' hp

theorem stepAtInput (leaf : Program 2) (payload value parameter : OTerm alpha)
    (hi : Nonempty (Derivation positive Delta (belowPayload leaf payload)))
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) := by
  apply programCases rawTag (Fin.cons value Fin.elim0) _
  intro beta j Theta tag hj ht
  rw [hasCompletionRename]
  simp only [consTermRename,emptyRename] at ht
  have hi' := renameInto hi j Theta hj
  have hp' := renameInto hp j Theta hj
  rw [belowPayloadRename] at hi'
  rw [graph1Rename] at hp'
  let xs : Fin 1 → OTerm beta := Fin.cons (value.relabel j) Fin.elim0
  apply equalityCases tag (numeral 2) _
  · intro Xi inc h2
    apply equalityCases tag (suc z) _
    · intro Omega inc2 h1
      have ht'' := weakenProof ht (fun p hp => inc2 p (inc p hp))
      have hraw2 := binaryValue InternalEqualityTest.equalityTest rawTag (two 1) z tag (numeral 2) xs
        (weakenProof h2 inc2) ht'' (twoValue xs)
      have hraw1 := binaryValue InternalEqualityTest.equalityTest rawTag (InternalLessThan.constantOne 1)
        z tag (suc z) xs h1 ht'' (InternalLessThanSupportProof.oneConstantValue xs)
      apply leafCase leaf _ _ _
      exact zeroBranchIntro _ _ _ (suc z) xs hraw2
        (zeroBranchIntro _ _ _ (suc z) xs hraw1 (InternalLessThanSupportProof.oneConstantValue xs))
    · intro Omega inc2 h1
      have he := InternalEqualityTestProof.equalityOfAcceptance tag (suc z) h1
      have ht1 := outputTransport rawTag tag (suc z) xs he
        (weakenProof ht (fun p hp => inc2 p (inc p hp)))
      exact lambdaCase leaf _ _ _ ht1
        (weakenProof hp' (fun p hp => inc2 p (inc p hp)))
        (weakenProof hi' (fun p hp => inc2 p (inc p hp)))
  · intro Xi inc h2
    have he := InternalEqualityTestProof.equalityOfAcceptance tag (numeral 2) h2
    have ht2 := outputTransport rawTag tag (numeral 2) xs he (weakenProof ht inc)
    exact applicationCase leaf _ _ _ ht2 (weakenProof hp' inc) (weakenProof hi' inc)

theorem payloadStep (leaf : Program 2) (payload : OTerm alpha)
    (hi : Nonempty (Derivation positive Delta (belowPayload leaf payload))) :
    Nonempty (Derivation positive Delta (AtPayload leaf payload)) := by
  apply atPayloadIntro leaf payload
  let value : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let Theta := graph1 InternalUnpair.right (payload.relabel Sum.inl) value ::
    Delta.map (fun q => q.relabel Sum.inl)
  have hi' := renameInto hi (Sum.inl : alpha → alpha ⊕ Fin 2) Theta (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [belowPayloadRename] at hi'
  obtain ⟨h⟩ := stepAtInput leaf (payload.relabel Sum.inl) value parameter hi'
    (show Nonempty (Derivation positive Theta (graph1 InternalUnpair.right (payload.relabel Sum.inl) value)) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem allPayload (leaf : Program 2) (payload : OTerm alpha) :
    Nonempty (Derivation positive Delta (AtPayload leaf payload)) := by
  apply payloadInduction leaf payload
  intro beta Theta p hi
  exact payloadStep leaf p hi

theorem hasCompletion (leaf : Program 2) (value parameter payload : OTerm alpha)
    (hp : Nonempty (Derivation positive Delta (graph1 InternalUnpair.right payload value))) :
    Nonempty (Derivation positive Delta (HasCompletion leaf value parameter payload)) :=
  atPayloadApply leaf payload value parameter (allPayload leaf payload) hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionInductionProof
