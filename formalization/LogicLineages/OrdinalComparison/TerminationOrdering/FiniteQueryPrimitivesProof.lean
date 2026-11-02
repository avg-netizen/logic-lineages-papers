module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open Source.SourceTypeSupport Source.SourceFreeOccurrences Source.SourcePortContexts Source.SourceOpenedObservations
open RecursiveComparison ComparisonFreeVariables FiniteQueryPrimitives FiniteQueryPrimitivesSupportProof

theorem literalHeadCalibration : FiniteQueryPrimitivesTargets.LiteralHeadCalibration := FiniteQueryPrimitivesSupportProof.literalHeadCalibration

theorem initialFrame : FiniteQueryPrimitivesTargets.InitialFrame := by
  intro Symbol arity Γ σ τ s t
  have hc : SubtypeClosed (fun υ => υ ∈ inputTypes s t) := by
    intro υ hυ χ hχ
    rcases Finset.mem_union.mp hυ with hs | ht
    · exact Finset.mem_union_left _ (Source.SourceTypeSupportProof.subtypeClosedSupport Symbol arity Γ σ s υ hs χ hχ)
    · exact Finset.mem_union_right _ (Source.SourceTypeSupportProof.subtypeClosedSupport Symbol arity Γ τ t υ ht χ hχ)
  refine ⟨hc,?_,?_,?_,?_⟩
  · exact (TypeClosureProof.literalEmbeddingTypeClosure Symbol arity _ Γ σ s hc).mpr (fun υ hυ => Finset.mem_union_left _ hυ)
  · exact (literalHeadCalibration Symbol arity Γ σ (embed s) _).mpr (by intros; assumption)
  · apply (ComparisonFreeVariablesProof.supportCalibration Symbol arity Γ σ (embed s) (inputNames s t)).mpr
    intro v hv
    rw [ComparisonFreeVariablesProof.ordinaryOccurrenceCalibration Symbol arity Γ σ s] at hv
    exact List.mem_append.mpr (Or.inl hv)
  · exact Source.SourceOpenedObservationsProof.openedRootMembership Symbol arity Γ τ t (lambdaDepth t) (Nat.le_refl _)

theorem everySelectAttemptClosure : FiniteQueryPrimitivesTargets.EverySelectAttemptClosure := by
  intro Symbol arity Γ K P a f base extraTypes extras τ request hc hK hP ha
  have selected : typesAllowed K request.selected ∧ headsAllowed P request.selected ∧ Supported request.selected a := by
    rcases List.mem_append.mp request.selectedMember with hb | he
    · exact ⟨(argumentTypeMembership K base).mp hK.2.1 _ hb,
        (argumentHeadMembership P base).mp hP.2.1 _ hb,
        (ComparisonFreeVariablesSyntaxProof.argumentsListSupported base a).mp ha.1 _ hb⟩
    · exact ⟨(argumentTypeMembership K extras).mp hK.2.2 _ he,
        (argumentHeadMembership P extras).mp hP.2.2 _ he,
        (ComparisonFreeVariablesSyntaxProof.argumentsListSupported extras a).mp ha.2 _ he⟩
  have hselected := rootType request.selected selected.1
  have hdecomp : K (arrows request.suppliedTypes τ) := request.suffix ▸ hselected
  obtain ⟨hsuffix,hresult⟩ := suffixTypes hc request.suppliedTypes τ hdecomp
  obtain ⟨hargsK,hargsP,hargsA⟩ := selfPayload K P a f base extraTypes extras τ hK hP ha request.suppliedTypes hsuffix
  refine ⟨hselected,hsuffix,hresult,selected.1,selected.2.1,selected.2.2,hargsK,hargsP,hargsA,?_⟩
  intro result he
  refine ⟨?_,?_,?_⟩
  · exact TypeClosureProof.simultaneousApplicationTypeClosure Symbol arity K Γ Γ _ τ request.suppliedTypes request.selected
      (fun v => .var v) (attemptArguments request) request.suffix result hc selected.1 (fun {_} _ h => h) hargsK he
  · exact LogicLineages.OrdinalComparison.TerminationOrdering.Proof.simultaneousApplicationHeadClosure Symbol arity P Γ Γ _ τ request.suppliedTypes request.selected
      (fun v => .var v) (attemptArguments request) request.suffix result selected.2.1 (fun {_} _ => True.intro) hargsP he
  · exact ComparisonFreeVariablesProof.originalApplyProvenance Symbol arity Γ Γ _ τ request.suppliedTypes request.selected
      (fun v => .var v) (attemptArguments request) request.suffix result a a selected.2.2 (by intros; assumption) hargsA he

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteQueryPrimitivesProof
