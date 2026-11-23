module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedChildStageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverThinChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedParentStageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro coverRename)
open NumberedWindowInternalCoverGrammarStageTargets (termsGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm installedCover)
open NumberedWindowInternalFactoredAuxOwnCoverThinChecks (exact_OpenFactoredAuxCoverAtTerms)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (pairRename)
open NumberedWindowInternalMeasuredUnrestrictedChildStageProof (exact_OpenUnrestrictedStageTermsCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Exact outstanding transport on the very same physical layer callbacks.
Neither a new grammar nor numerical agreement of grammars suffices. -/
def StageTermTransport (P : Program 5) (A : Program 2) (s : Settings) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α))
    (d b D M source target key : OTerm α),
    Nonempty (Derivation body Γ (termsGraph P A source d (headsTerm s α) (typesTerm s α) b)) →
    Nonempty (Derivation body Γ (termsGraph P A target D (headsTerm s α) (typesTerm s α) M)) →
    Nonempty (Derivation body Γ (ltF d (suc D))) →
    Nonempty (Derivation body Γ (ltF b (suc M))) →
    Nonempty (Derivation body Γ (memberGraph source key)) →
    Nonempty (Derivation body Γ (memberGraph target key))

theorem stageTermsRename {β : Type} (P : Program 5) (A : Program 2) (s : Settings)
    (out d w : OTerm α) (j : α → β) :
    (termsGraph P A out d (headsTerm s α) (typesTerm s α) w).relabel j =
      termsGraph P A (out.relabel j) (d.relabel j) (headsTerm s β) (typesTerm s β) (w.relabel j) := by
  simp only [termsGraph,programRename,quadInputsRename,headsTerm,typesTerm,numeralRename]

/-- Open the actual successor stage, once the two true memberships at its
common exact predecessor are obtained. Both scratch and own occurrence are
returned together in the original object existential. -/
theorem exact_OpenUnrestrictedParentOwnAtCommonStage (V M : Program 1) (P : Program 5) (A : Program 2)
    (s : Settings) (dom cod fn arg p depth width prev : OTerm α)
    (valid : Nonempty (Derivation B Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg))))
    (measured : Nonempty (Derivation B Γ (unary M p (auxiliaryTerm dom cod fn arg))))
    (coords : Nonempty (Derivation B Γ (codePair p (suc depth) width)))
    (prior : Nonempty (Derivation B Γ (termsGraph P A prev depth (headsTerm s α) (typesTerm s α) width)))
    (domIn : Nonempty (Derivation B Γ (memberGraph (typesTerm s α) dom)))
    (codIn : Nonempty (Derivation B Γ (memberGraph (typesTerm s α) cod)))
    (fnIn : Nonempty (Derivation B Γ (memberGraph prev fn)))
    (argIn : Nonempty (Derivation B Γ (memberGraph prev arg))) :
    Nonempty (Derivation B Γ (occursInCover (installedCover V M P A) s
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenUnrestrictedStageTermsCases P A s (suc depth) width _
  intro β j Δ vertices keep following
  rw [coverRename,auxiliaryRename]
  rw [sucRelabel] at following
  have v := renameInto valid j Δ keep
  have m := renameInto measured j Δ keep
  have c := renameInto coords j Δ keep
  have r := renameInto prior j Δ keep
  have hd := renameInto domIn j Δ keep
  have hc := renameInto codIn j Δ keep
  have hf := renameInto fnIn j Δ keep
  have ha := renameInto argIn j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at v
  simp only [unaryRename,auxiliaryRename] at m
  simp only [pairRename,sucRelabel] at c
  rw [stageTermsRename] at r
  simp only [graphRename,typesTerm,numeralRename] at hd hc
  rw [graphRename] at hf ha
  obtain ⟨reports⟩ := exact_OpenFactoredAuxCoverAtTerms V M P A s B β Δ
    (p.relabel j) (depth.relabel j) (width.relabel j) (prev.relabel j) vertices
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j) v m c r following hd hc hf ha
  have together := Derivation.conjunctionRight reports
  let q := auxiliaryTerm (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
  exact coverIntro (installedCover V M P A) s q q vertices
    ⟨Derivation.conjunctionLeft together⟩ ⟨Derivation.conjunctionRight together⟩

/-- The exact local cross-bound rule reduces both child occurrences to one
genuine reported predecessor, chosen on the original physical callback. -/
theorem exact_OpenUnrestrictedParentOwnAtBounds (V M : Program 1) (P : Program 5) (A : Program 2)
    (s : Settings) (dom cod fn arg p depth width df bf da ba fs ats : OTerm α)
    (lift : StageTermTransport P A s)
    (valid : Nonempty (Derivation B Γ (unary V (suc z) (auxiliaryTerm dom cod fn arg))))
    (measured : Nonempty (Derivation B Γ (unary M p (auxiliaryTerm dom cod fn arg))))
    (coords : Nonempty (Derivation B Γ (codePair p (suc depth) width)))
    (fnStage : Nonempty (Derivation B Γ (termsGraph P A fs df (headsTerm s α) (typesTerm s α) bf)))
    (argStage : Nonempty (Derivation B Γ (termsGraph P A ats da (headsTerm s α) (typesTerm s α) ba)))
    (fnDepth : Nonempty (Derivation B Γ (ltF df (suc depth))))
    (argDepth : Nonempty (Derivation B Γ (ltF da (suc depth))))
    (fnWidth : Nonempty (Derivation B Γ (ltF bf (suc width))))
    (argWidth : Nonempty (Derivation B Γ (ltF ba (suc width))))
    (domIn : Nonempty (Derivation B Γ (memberGraph (typesTerm s α) dom)))
    (codIn : Nonempty (Derivation B Γ (memberGraph (typesTerm s α) cod)))
    (fnIn : Nonempty (Derivation B Γ (memberGraph fs fn)))
    (argIn : Nonempty (Derivation B Γ (memberGraph ats arg))) :
    Nonempty (Derivation B Γ (occursInCover (installedCover V M P A) s
      (auxiliaryTerm dom cod fn arg) (auxiliaryTerm dom cod fn arg))) := by
  apply exact_OpenUnrestrictedStageTermsCases P A s depth width _
  intro β j Δ prev keep here
  rw [coverRename,auxiliaryRename]
  have v := renameInto valid j Δ keep
  have m := renameInto measured j Δ keep
  have c := renameInto coords j Δ keep
  have f := renameInto fnStage j Δ keep
  have a := renameInto argStage j Δ keep
  have fD := renameInto fnDepth j Δ keep
  have aD := renameInto argDepth j Δ keep
  have fW := renameInto fnWidth j Δ keep
  have aW := renameInto argWidth j Δ keep
  have hd := renameInto domIn j Δ keep
  have hc := renameInto codIn j Δ keep
  have hf := renameInto fnIn j Δ keep
  have ha := renameInto argIn j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at v
  simp only [unaryRename,auxiliaryRename] at m
  simp only [pairRename,sucRelabel] at c
  rw [stageTermsRename] at f a
  simp only [orderRename,sucRelabel] at fD aD fW aW
  simp only [graphRename,typesTerm,numeralRename] at hd hc
  rw [graphRename] at hf ha
  have fnHere := lift B β Δ (df.relabel j) (bf.relabel j) (depth.relabel j) (width.relabel j)
    (fs.relabel j) prev (fn.relabel j) f here fD fW hf
  have argHere := lift B β Δ (da.relabel j) (ba.relabel j) (depth.relabel j) (width.relabel j)
    (ats.relabel j) prev (arg.relabel j) a here aD aW ha
  exact exact_OpenUnrestrictedParentOwnAtCommonStage V M P A s
    (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (p.relabel j) (depth.relabel j) (width.relabel j) prev v m c here hd hc fnHere argHere

#print axioms stageTermsRename
#print axioms exact_OpenUnrestrictedParentOwnAtCommonStage
#print axioms exact_OpenUnrestrictedParentOwnAtBounds
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedParentStageProof
