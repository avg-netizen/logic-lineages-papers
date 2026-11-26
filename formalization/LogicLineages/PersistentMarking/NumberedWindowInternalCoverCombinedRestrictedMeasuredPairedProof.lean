module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedAuxKernelProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredAuxExchangeCompareProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph exchangeTape)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange compareMeasurements)
open NumberedWindowInternalMeasuredAuxExchangeCompareProof (compareShared compareCases)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
  (auxiliaryTermRename exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxProof (exact_OpenCoverCombinedRestrictedPairedAux)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxKernelProof (guardedOfActualPair)
open NumberedWindowInternalCoverCombinedRestrictedRoundApplicationCombinedProof (pairedParentEdges)
open NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedTargets

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

/-- Step 1 (generic): an accepted edge of the measured exchange over `D` is an
accepted edge of `D` together with the measure comparison on the same tape. -/
theorem measuredParentEdge {α : Type} {Γ : List (Formula α)} (N : Program 1) (D : Program 2)
    (W : Program 3) (ctx ty w k : OTerm α)
    (e : Nonempty (Derivation body Γ (edgeGraph (measuredExchange N D) W ctx ty w k))) :
    Nonempty (Derivation body Γ (edgeGraph D W ctx ty w k)) ∧
      Nonempty (Derivation body Γ
        (programGraph (compareMeasurements N) (suc z) (exchangeTape w k))) := by
  obtain ⟨e⟩ := e
  obtain ⟨lawM⟩ := exact_OpenPackedScalarEdge (measuredExchange N D) W body α Γ ctx ty w k
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft lawM) e
  obtain ⟨mm⟩ := conjunctionRecover D (compareMeasurements N) (exchangeTape w k)
    ⟨Derivation.conjunctionLeft calls⟩
  obtain ⟨lawD⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx ty w k
  exact ⟨⟨Derivation.implicationElimination (Derivation.conjunctionRight lawD)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft mm)
        (Derivation.conjunctionRight calls))⟩,
    ⟨Derivation.conjunctionRight mm⟩⟩

/-- Steps 3b–5 (generic in cover, settings, measure, base exchange and window):
an accepted edge of the unmeasured guarded paired exchange, one common cover
option and one common measure of its two endpoints give the accepted edge of
the measured guarded paired exchange between the same endpoints. -/
theorem measuredUpgrade {α : Type} {Γ : List (Formula α)} (C : Program 3) (s : Settings)
    (N : Program 1) (D : Program 2) (W : Program 3) (ctx ty a b p out : OTerm α)
    (e : Nonempty (Derivation body Γ
      (edgeGraph (guardedExchange C s (thinPairedExchange D)) W ctx ty a b)))
    (ca : Nonempty (Derivation body Γ (unary (coverOption C s) out a)))
    (cb : Nonempty (Derivation body Γ (unary (coverOption C s) out b)))
    (pa : Nonempty (Derivation body Γ (unary N p a)))
    (pb : Nonempty (Derivation body Γ (unary N p b))) :
    Nonempty (Derivation body Γ
      (edgeGraph (guardedExchange C s (thinPairedExchange (measuredExchange N D))) W ctx ty a b)) := by
  have edges := pairedParentEdges C s D W ctx ty a b e
  obtain ⟨fwd⟩ := edges.1
  obtain ⟨rev⟩ := edges.2
  obtain ⟨lawF⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx ty a b
  obtain ⟨lawR⟩ := exact_OpenPackedScalarEdge D W body α Γ ctx ty b a
  have ab := Derivation.implicationElimination (Derivation.conjunctionLeft lawF) fwd
  have ba := Derivation.implicationElimination (Derivation.conjunctionLeft lawR) rev
  have dab : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape a b))) :=
    ⟨Derivation.conjunctionLeft ab⟩
  have dba : Nonempty (Derivation body Γ (programGraph D (suc z) (exchangeTape b a))) :=
    ⟨Derivation.conjunctionLeft ba⟩
  have mab : Nonempty (Derivation body Γ
      (programGraph (measuredExchange N D) (suc z) (exchangeTape a b))) :=
    conjunctionAccept D (compareMeasurements N) (exchangeTape a b) dab (compareShared N a b p pa pb)
  have mba : Nonempty (Derivation body Γ
      (programGraph (measuredExchange N D) (suc z) (exchangeTape b a))) :=
    conjunctionAccept D (compareMeasurements N) (exchangeTape b a) dba (compareShared N b a p pb pa)
  obtain ⟨physical⟩ := guardedOfActualPair C s (measuredExchange N D) a b out mab mba ca cb
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge
    (guardedExchange C s (thinPairedExchange (measuredExchange N D))) W body α Γ ctx ty a b
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight law)
    (Derivation.conjunctionIntroduction physical (Derivation.conjunctionRight ab))⟩

/-- The measured application edge from the two directed function edges and a
common selected measure of the two *applications* (measured analogue of #1386). -/
theorem measuredEdgeOfApplicationMeasure
    (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    {α : Type} (Γ : List (Formula α)) (ctx dom cod f g arg p : OTerm α) :
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
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) p a)) →
    Nonempty (Derivation body Γ (unary (selectedMeasure P.R) p b)) →
    Nonempty (Derivation body Γ (edgeGraph Xm W ctx cod a b)) := by
  intro P W D Xm a b syn ty argument fg gf pa pb
  apply exact_OpenCoverCombinedRestrictedPairedAux V TV M M0 B T base s body α Γ
    ctx dom cod f g arg p (edgeGraph Xm W ctx cod a b) syn ty argument fg gf pa pb
  intro β j Δ vertices keep ca cb e
  have pa' := renameInto pa j Δ keep
  have pb' := renameInto pb j Δ keep
  rw [unaryRename] at pa' pb'
  show Nonempty (Derivation body Δ ((edgeGraph Xm W ctx cod a b).relabel j))
  rw [edgeRename]
  exact measuredUpgrade P.cover s (selectedMeasure P.R) D W (ctx.relabel j) (cod.relabel j)
    (a.relabel j) (b.relabel j) (p.relabel j) (suc vertices) e ca cb pa' pb'

/-- The measured application edge from the two directed function edges and a
common selected measure of the two *functions* (measured analogue of
`ExactOpenCoverCombinedRestrictedPairedSharedMeasureEdge`). -/
theorem measuredEdgeOfFunctionMeasure
    (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (base : Program 2) (s : Settings)
    {α : Type} (Γ : List (Formula α)) (ctx dom cod f g arg m : OTerm α) :
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
    Nonempty (Derivation body Γ (edgeGraph Xm W ctx cod a b)) := by
  intro P W D Xm a b syn ty argument fg gf cf cg
  apply exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent V TV M M0 B T s body α Γ
    dom cod f g arg m (edgeGraph Xm W ctx cod a b) cf cg
  intro β j Δ p keep pa pb
  have mv := move Δ j keep TV _ D W ctx dom cod f g arg syn ty argument fg gf
  have pa' : Nonempty (Derivation body Δ (unary (selectedMeasure P.R) p
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) (f.relabel j) (arg.relabel j)))) := by
    rw [← auxiliaryTermRename]
    exact pa
  have pb' : Nonempty (Derivation body Δ (unary (selectedMeasure P.R) p
      (auxiliaryTerm (dom.relabel j) (cod.relabel j) (g.relabel j) (arg.relabel j)))) := by
    rw [← auxiliaryTermRename]
    exact pb
  have e := measuredEdgeOfApplicationMeasure (body := body) V TV M M0 B T base s Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j) (arg.relabel j) p
    mv.syn mv.ty mv.argument mv.fg mv.gf pa' pb'
  show Nonempty (Derivation body Δ
    ((edgeGraph Xm W ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg)).relabel j))
  rw [edgeRename,auxiliaryTermRename,auxiliaryTermRename]
  exact e

theorem exact_OpenCoverCombinedRestrictedMeasuredPairedEdge :
    ExactOpenCoverCombinedRestrictedMeasuredPairedEdge := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg P W Xm a b syn ty argument fgm
  let N := selectedMeasure P.R
  let D := directedX base P.V
  have edges := pairedParentEdges P.cover s (measuredExchange N D) W ctx (rawCons dom cod) f g fgm
  have uf := measuredParentEdge N D W ctx (rawCons dom cod) f g edges.1
  have ug := measuredParentEdge N D W ctx (rawCons dom cod) g f edges.2
  apply compareCases N f g (edgeGraph Xm W ctx cod a b) uf.2
  intro β j Δ m keep mf mg
  have mv := move Δ j keep TV _ D W ctx dom cod f g arg syn ty argument uf.1 ug.1
  have e := measuredEdgeOfFunctionMeasure (body := body) V TV M M0 B T base s Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j) (arg.relabel j) m
    mv.syn mv.ty mv.argument mv.fg mv.gf mf mg
  show Nonempty (Derivation body Δ
    ((edgeGraph Xm W ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg)).relabel j))
  rw [edgeRename,auxiliaryTermRename,auxiliaryTermRename]
  exact e

#print axioms measuredParentEdge
#print axioms measuredUpgrade
#print axioms measuredEdgeOfFunctionMeasure
#print axioms exact_OpenCoverCombinedRestrictedMeasuredPairedEdge
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredPairedProof
