module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureEqualityProof
  (auxiliaryTermRename exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent)
open NumberedWindowInternalCoverCombinedRestrictedPairedMinimumProof
  (exact_OpenCoverCombinedRestrictedPairedEdge)
open NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastProof
  (exact_OpenCoverCombinedRestrictedPairedCommonLeast)
open NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureTargets

attribute [local irreducible] programGraph

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

theorem exact_OpenCoverCombinedRestrictedPairedSharedMeasureEdge :
    ExactOpenCoverCombinedRestrictedPairedSharedMeasureEdge := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m P W D X a b syn ty argument fg gf cf cg
  apply exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent V TV M M0 B T s body α Γ
    dom cod f g arg m (edgeGraph X W ctx cod a b) cf cg
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
  have e := exact_OpenCoverCombinedRestrictedPairedEdge V TV M M0 B T base s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j) (arg.relabel j) p
    mv.syn mv.ty mv.argument mv.fg mv.gf pa' pb'
  show Nonempty (Derivation body Δ
    ((edgeGraph X W ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg)).relabel j))
  rw [edgeRename,auxiliaryTermRename,auxiliaryTermRename]
  exact e

theorem exact_OpenCoverCombinedRestrictedPairedSharedMeasureCommonLeast :
    ExactOpenCoverCombinedRestrictedPairedSharedMeasureCommonLeast := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal P W D X a b syn ty argument fg gf
    cf cg k
  apply exact_OpenCoverCombinedRestrictedPairedSharedMeasureParent V TV M M0 B T s body α Γ
    dom cod f g arg m goal cf cg
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
  apply exact_OpenCoverCombinedRestrictedPairedCommonLeast V TV M M0 B T base s body β Δ
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j) (arg.relabel j) p
    (goal.relabel j) mv.syn mv.ty mv.argument mv.fg mv.gf pa' pb'
  intro γ i Θ x retain la lb
  have both (q : Formula α) (hq : q ∈ Γ) : q.relabel (i ∘ j) ∈ Θ := by
    rw [← formulaRelabelComposition j i q]
    exact retain (q.relabel j) (keep q hq)
  rw [formulaRelabelComposition j i goal]
  rw [← auxiliaryTermRename] at la
  rw [← auxiliaryTermRename] at lb
  simp only [Term.relabel_relabel] at la lb
  exact k γ (i ∘ j) Θ x both la lb

#print axioms exact_OpenCoverCombinedRestrictedPairedSharedMeasureEdge
#print axioms exact_OpenCoverCombinedRestrictedPairedSharedMeasureCommonLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedSharedMeasureProof
