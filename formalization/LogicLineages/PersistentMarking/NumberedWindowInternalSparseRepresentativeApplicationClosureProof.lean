module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundObservationSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationClosureProof
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
attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3)

private theorem atEdge (law : FunctionEdgeAt C s X W)
    (ctx dom cod arg f g value : OTerm α)
    (edge : Nonempty (Derivation body Γ (acceptEdge (edge4 X W) ctx (rawCons dom cod) f g)))
    (initial : Nonempty (Derivation body Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod f arg) value)))
    (reports : Derivation body Γ (guards C s W ctx cod (auxiliaryTerm dom cod f arg) (auxiliaryTerm dom cod g arg))) :
    Nonempty (Derivation body Γ (leastGraph C X W s ctx cod (auxiliaryTerm dom cod g arg) value)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let a := auxiliaryTerm dom cod f arg
  let b := auxiliaryTerm dom cod g arg
  let t : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := unary (coverOption C s) t (a.relabel j) ⊓ unary (coverOption C s) t (b.relabel j)
  let Δ := row :: Γ.map weaken
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have windows := renameInto ⟨Derivation.conjunctionLeft reports⟩ j Δ keep
  simp only [conjunctionRename,windowRename,auxiliaryRename] at windows
  have child := renameInto edge j Δ keep
  simp only [acceptEdge,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel,rawConsRename] at child
  have start := renameInto initial j Δ keep
  simp only [leastRename,auxiliaryRename] at start
  have report : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  change Derivation body Δ (unary (coverOption C s) t (a.relabel j) ⊓ unary (coverOption C s) t (b.relabel j)) at report
  simp only [a,b,auxiliaryRename] at report
  obtain ⟨windows⟩ := windows
  obtain ⟨child⟩ := child
  obtain ⟨start⟩ := start
  obtain ⟨rule⟩ := law body _ Δ (ctx.relabel j) (dom.relabel j) (cod.relabel j) (f.relabel j) (g.relabel j)
    (arg.relabel j) t t (value.relabel j)
  have both := Derivation.implicationElimination rule (Derivation.conjunctionIntroduction child
    (Derivation.conjunctionIntroduction windows (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft report)
      (Derivation.conjunctionIntroduction (Derivation.conjunctionRight report) (Derivation.equalityReflexivity (emb t))))))
  have next := Derivation.implicationElimination (Derivation.conjunctionRight both) start
  have final : Derivation body Δ (weaken (leastGraph C X W s ctx cod b value)) := by
    change Derivation body Δ ((leastGraph C X W s ctx cod b value).relabel j)
    simpa only [b,leastRename,auxiliaryRename] using next
  exact ⟨Derivation.existentialElimination (Derivation.conjunctionRight reports) final⟩

theorem localClosure (law : FunctionEdgeAt C s X W) (ctx dom cod arg value : OTerm α)
    (support : Nonempty (Derivation body Γ (supports C X W s ctx dom cod arg value))) :
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
  obtain ⟨ready⟩ := openBlock (supportRow C X W s ctx dom cod arg value) support
  have accepted := Derivation.conjunctionLeft h
  have val := Derivation.conjunctionRight h
  change Derivation body Δ (observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) f ((suc value).relabel j)) at val
  rw [sucRelabel] at val
  obtain ⟨start⟩ := (observerGraph (packedLeastProgram C X W s) body _ Δ _ _ _ _ f _).mp ⟨val⟩
  have req := Derivation.implicationElimination (addHyp ready A) (Derivation.conjunctionIntroduction accepted start)
  change Derivation body Δ (acceptEdge (edge4 X W) (ctx.relabel j) ((rawCons dom cod).relabel j) f g) at accepted
  rw [rawConsRename] at accepted
  have next := atEdge C s X W law _ _ _ _ f g _ ⟨accepted⟩ ⟨start⟩ req
  obtain ⟨seen⟩ := (observerGraph (packedLeastProgram C X W s) body _ Δ _ _ _ _ g _).mpr next
  have result : Derivation body Δ (observed M (ctx.relabel j) (dom.relabel j) (cod.relabel j) (arg.relabel j) g ((suc value).relabel j)) := by
    rw [sucRelabel]
    exact seen
  exact ⟨Derivation.implicationIntroduction result⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRepresentativeApplicationClosureProof
