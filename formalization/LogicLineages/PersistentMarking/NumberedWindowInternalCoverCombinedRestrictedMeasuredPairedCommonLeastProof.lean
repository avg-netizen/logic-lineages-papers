module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseAdjacentMinimumChecks (exact_MutualEdgeMinimumEquality)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename casesLeast)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
  (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalMeasuredAuxExchangeCompareProof (compareCases)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof (auxiliaryTermRename)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof (pairedParentEdges)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
  (measuredParentEdge measuredEdgeOfFunctionMeasure)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)}

private theorem edgeRename {α β : Type} (X : Program 2) (W : Program 3) (ctx ty a b : OTerm α)
    (j : α → β) :
    (edgeGraph X W ctx ty a b).relabel j =
      edgeGraph X W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [edgeGraph,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

/-- The five non-measure parent reports, moved into a continuation context. -/
private structure Moved {α β : Type} (body : Positive (Fin 1)) (Δ : List (Formula β)) (j : α → β)
    (TV G : Program 1) (D : Program 2) (W : Program 3) (ctx dom cod f g arg : OTerm α) : Prop where
  syn : Nonempty (Derivation body Δ
    (unary TV (suc z) (dom.relabel j) ⊓ unary TV (suc z) (cod.relabel j)))
  ty : Nonempty (Derivation body Δ
    (unary G (suc z) (dom.relabel j) ⊓ unary G (suc z) (cod.relabel j)))
  argument : Nonempty (Derivation body Δ
    (windowAt W (ctx.relabel j) (dom.relabel j) (arg.relabel j)))
  fg : Nonempty (Derivation body Δ
    (edgeGraph D W (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (f.relabel j) (g.relabel j)))
  gf : Nonempty (Derivation body Δ
    (edgeGraph D W (ctx.relabel j) (rawCons (dom.relabel j) (cod.relabel j)) (g.relabel j) (f.relabel j)))

private theorem move {α β : Type} {body : Positive (Fin 1)} {Γ : List (Formula α)}
    (Δ : List (Formula β)) (j : α → β) (keep : ∀ p ∈ Γ, p.relabel j ∈ Δ)
    (TV G : Program 1) (D : Program 2) (W : Program 3) (ctx dom cod f g arg : OTerm α)
    (syn : Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)))
    (ty : Nonempty (Derivation body Γ (unary G (suc z) dom ⊓ unary G (suc z) cod)))
    (argument : Nonempty (Derivation body Γ (windowAt W ctx dom arg)))
    (fg : Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) f g)))
    (gf : Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) g f))) :
    Moved body Δ j TV G D W ctx dom cod f g arg := by
  have syn' := renameInto syn j Δ keep
  have ty' := renameInto ty j Δ keep
  have argument' := renameInto argument j Δ keep
  have fg' := renameInto fg j Δ keep
  have gf' := renameInto gf j Δ keep
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel] at syn' ty'
  rw [windowRename] at argument'
  simp only [edgeRename,rawConsRename] at fg' gf'
  exact ⟨syn',ty',argument',fg',gf'⟩

/-- Re-derived from the (private) helper of the PairedCommonLeast proof; it is
generic in the base exchange under the cover guard. -/
private theorem shareLeast {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3) (ctx ty a b x : OTerm α)
    (ab : Nonempty (Derivation body Γ (edgeGraph (guardedExchange C s baseX) W ctx ty a b)))
    (ba : Nonempty (Derivation body Γ (edgeGraph (guardedExchange C s baseX) W ctx ty b a)))
    (la : Nonempty (Derivation body Γ (leastGraph C (guardedExchange C s baseX) W s ctx ty a x)))
    (hb : Nonempty (Derivation body Γ (hasLeast C (guardedExchange C s baseX) W s ctx ty b))) :
    Nonempty (Derivation body Γ (leastGraph C (guardedExchange C s baseX) W s ctx ty b x)) := by
  let X := guardedExchange C s baseX
  apply casesLeast C X W s ctx ty b (leastGraph C X W s ctx ty b x) hb
  intro β i Θ y keep ly
  rw [leastRename]
  have ab' := renameInto ab i Θ keep
  have ba' := renameInto ba i Θ keep
  have la' := renameInto la i Θ keep
  rw [edgeRename] at ab' ba'
  rw [leastRename] at la'
  obtain ⟨ab'⟩ := ab'
  obtain ⟨ba'⟩ := ba'
  obtain ⟨la'⟩ := la'
  obtain ⟨ly⟩ := ly
  obtain ⟨law⟩ := exact_MutualEdgeMinimumEquality C s baseX W body β Θ
    (ctx.relabel i) (ty.relabel i) (a.relabel i) (b.relabel i) (x.relabel i) y
  have eq : Derivation body Θ (eqn (x.relabel i) y) :=
    Derivation.implicationElimination law (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction la' ly) (Derivation.conjunctionIntroduction ab' ba'))
  exact outputTransport (packedLeastProgram C X W s) (suc y) (suc (x.relabel i))
    ![ctx.relabel i,ty.relabel i,b.relabel i] ⟨congSuc (symm eq)⟩ ⟨ly⟩

/-- The common least over the measured exchange from the two directed function
edges and a common selected measure of the two functions (measured analogue of
`ExactOpenCoverCombinedRestrictedPairedSharedMeasureCommonLeast`). -/
theorem measuredCommonLeastOfFunctionMeasure
    (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    {α : Type} (Γ : List (Formula α)) (ctx dom cod f g arg m : OTerm α) (goal : Formula α) :
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    let D := directedX base P.V
    let Xm := guardedExchange P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D))
    let a := auxiliaryTerm dom cod f arg
    let b := auxiliaryTerm dom cod g arg
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) f g)) →
    Nonempty (Derivation body Γ (edgeGraph D W ctx (rawCons dom cod) g f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m f)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) m g)) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (x : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation body Δ
        (leastGraph P.cover Xm W s (ctx.relabel j) (cod.relabel j) (a.relabel j) x)) →
      Nonempty (Derivation body Δ
        (leastGraph P.cover Xm W s (ctx.relabel j) (cod.relabel j) (b.relabel j) x)) →
      Nonempty (Derivation body Δ (goal.relabel j))) →
    Nonempty (Derivation body Γ goal) := by
  intro P W D Xm a b syn ty argument fg gf cf cg k
  have ab := measuredEdgeOfFunctionMeasure (body := body) V TV M M0 B T base s Γ
    ctx dom cod f g arg m syn ty argument fg gf cf cg
  have ba := measuredEdgeOfFunctionMeasure (body := body) V TV M M0 B T base s Γ
    ctx dom cod g f arg m syn ty argument gf fg cg cf
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge Xm W body α Γ ctx cod a b
  obtain ⟨abd⟩ := ab
  have windows := Derivation.conjunctionRight
    (Derivation.implicationElimination (Derivation.conjunctionLeft law) abd)
  obtain ⟨repA⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V Xm s body α Γ ctx cod a
    ⟨Derivation.conjunctionLeft windows⟩
  obtain ⟨repB⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V Xm s body α Γ ctx cod b
    ⟨Derivation.conjunctionRight windows⟩
  apply casesLeast P.cover Xm W s ctx cod a goal ⟨Derivation.conjunctionRight repA⟩
  intro β j Δ x keep la
  have hb := renameInto ⟨Derivation.conjunctionRight repB⟩ j Δ keep
  rw [hasRename] at hb
  have ab' := renameInto ⟨abd⟩ j Δ keep
  have ba' := renameInto ba j Δ keep
  rw [edgeRename] at ab' ba'
  have lb := shareLeast P.cover s (thinPairedExchange (measuredExchange (selectedMeasure P.R) D)) W
    (ctx.relabel j) (cod.relabel j) (a.relabel j) (b.relabel j) x ab' ba' la hb
  exact k β j Δ x keep la lb

theorem exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast :
    ExactOpenCoverCombinedRestrictedMeasuredPairedCommonLeast := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg goal P W Xm a b syn ty argument fgm k
  let N := selectedMeasure P.R
  let D := directedX base P.V
  have edges := pairedParentEdges P.cover s (measuredExchange N D) W ctx (rawCons dom cod) f g fgm
  have uf := measuredParentEdge N D W ctx (rawCons dom cod) f g edges.1
  have ug := measuredParentEdge N D W ctx (rawCons dom cod) g f edges.2
  apply compareCases N f g goal uf.2
  intro β j Δ m keep mf mg
  have mv := move Δ j keep TV _ D W ctx dom cod f g arg syn ty argument uf.1 ug.1
  apply measuredCommonLeastOfFunctionMeasure (body := body) V TV M M0 B T base s Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j) (arg.relabel j) m
    (goal.relabel j) mv.syn mv.ty mv.argument mv.fg mv.gf mf mg
  intro γ i Θ x retain la lb
  have both (q : Formula α) (hq : q ∈ Γ) : q.relabel (i ∘ j) ∈ Θ := by
    rw [← formulaRelabelComposition j i q]
    exact retain (q.relabel j) (keep q hq)
  rw [formulaRelabelComposition j i goal]
  rw [← auxiliaryTermRename] at la
  rw [← auxiliaryTermRename] at lb
  simp only [Term.relabel_relabel] at la lb
  exact k γ (i ∘ j) Θ x both la lb

#print axioms measuredCommonLeastOfFunctionMeasure
#print axioms exact_OpenCoverCombinedRestrictedMeasuredPairedCommonLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedCommonLeastProof
