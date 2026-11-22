module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationChecks
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb sucRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalClosedProgramsBindingProof (introduction)
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge edgeTape)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseStructuralApplicationTargets (FunctionEdgeAt)
open NumberedWindowInternalSparseRoundObservationTargets (closed edgeRow observed)
open NumberedWindowInternalSparseRepresentativeApplicationTargets
open NumberedWindowInternalSparseRepresentativeApplicationGraphProof (openBlock observerGraph)
open NumberedWindowInternalSparseMeasuredInstallationTargets (FunctionApplicationAt)
open NumberedWindowInternalSparseFormationRepresentativeTargets
open NumberedWindowInternalSparseFormationRepresentativeSyntaxProof (formationRename atFunction)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseRoundObservationChecks (exact_SelectedObservation)
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3)

private theorem localClosure (law : FunctionApplicationAt C s X W) (ctx dom cod arg value : OTerm α)
    (support : Nonempty (Derivation body Γ (formation W ctx dom cod arg))) :
    Nonempty (Derivation body Γ (closed (edge4 X W) (applicationObserver (packedLeastProgram C X W s))
      ctx (rawCons dom cod) dom cod arg (suc value))) := by
  let j : α → α ⊕ Fin 2 := Sum.inl
  let f : OTerm (α ⊕ Fin 2) := .var (.inr 0)
  let g : OTerm (α ⊕ Fin 2) := .var (.inr 1)
  let M := applicationObserver (packedLeastProgram C X W s)
  let A := acceptEdge (edge4 X W) (ctx.relabel j) ((rawCons dom cod).relabel j) f g ⊓
    observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) f ((suc value).relabel j)
  let Δ := A :: Γ.map (fun p => p.relabel j)
  apply introduction body α 2 Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have ready := renameInto support j Δ (by
    intro q hq
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩))
  rw [formationRename] at ready
  obtain ⟨ready⟩ := ready
  have accepted := Derivation.conjunctionLeft h
  have val := Derivation.conjunctionRight h
  change Derivation body Δ (observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) f ((suc value).relabel j)) at val
  rw [sucRelabel] at val
  obtain ⟨start⟩ := (observerGraph (packedLeastProgram C X W s) body _ Δ _ _ _ _ f _).mp ⟨val⟩
  change Derivation body Δ (acceptEdge (edge4 X W) (ctx.relabel j) ((rawCons dom cod).relabel j) f g) at accepted
  rw [rawConsRename] at accepted
  obtain ⟨child⟩ := exact_OpenPackedScalarEdge X W body _ Δ (ctx.relabel j)
    (rawCons (dom.relabel j) (cod.relabel j)) f g
  have windows := Derivation.conjunctionRight
    (Derivation.implicationElimination (Derivation.conjunctionLeft child) accepted)
  obtain ⟨src⟩ := atFunction W _ _ _ _ f ready
  obtain ⟨dst⟩ := atFunction W _ _ _ _ g ready
  obtain ⟨applyEdge⟩ := law body _ Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) f g
    (arg.relabel j) (value.relabel j)
  have ws := Derivation.conjunctionIntroduction (Derivation.implicationElimination src (Derivation.conjunctionLeft windows))
    (Derivation.implicationElimination dst (Derivation.conjunctionRight windows))
  have applied := Derivation.implicationElimination applyEdge (Derivation.conjunctionIntroduction accepted ws)
  have next := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight applied) start)
  obtain ⟨seen⟩ := (observerGraph (packedLeastProgram C X W s) body _ Δ _ _ _ _ g _).mpr next
  have result : Derivation body Δ (observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) g ((suc value).relabel j)) := by
    rw [sucRelabel]
    exact seen
  exact ⟨Derivation.implicationIntroduction result⟩

theorem exact_FormationRepresentative : ExactFormationRepresentative := by
  intro C s X W law body α Γ ctx dom cod arg f repr value initial chosen final
  let least := packedLeastProgram C X W s
  let M := applicationObserver least
  let A := formation W ctx dom cod arg ⊓ (initial ⊓ chosen)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨closed⟩ := localClosure C s X W law ctx dom cod arg value ⟨Derivation.conjunctionLeft h⟩
  have runs := Derivation.conjunctionRight h
  obtain ⟨src⟩ := (observerGraph least body α Δ ctx dom cod arg f (suc value)).mpr
    ⟨Derivation.conjunctionLeft runs⟩
  obtain ⟨move⟩ := exact_SelectedObservation C X W s M body α Δ ctx (rawCons dom cod) dom cod arg f repr (suc value)
  have target := Derivation.implicationElimination move (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction closed src) (Derivation.conjunctionRight runs))
  obtain ⟨out⟩ := (observerGraph least body α Δ ctx dom cod arg repr (suc value)).mp ⟨target⟩
  exact ⟨Derivation.implicationIntroduction out⟩

#print axioms exact_FormationRepresentative
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFormationRepresentativeChecks
