module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedInductionDispatchTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionPointProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open ID1Completion.InternalClosedPrograms (allBlock)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs ParentRow)
open NumberedWindowInternalCoverRefinedInductionDispatchTransportProof (ownBelowRename)
open NumberedWindowInternalCoverOwnEarlierTargets
open NumberedWindowInternalCoverCombinedRestrictedInductionTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem ownAtActualMeasuredPoint (P : Programs) (s : Settings) (raw vertices ctx result : OTerm α)
    (step : PointOwnStep P s body)
    (earlier : Nonempty (Derivation body Γ (ownBelow P.V P.W P.cover s raw)))
    (valid : Nonempty (Derivation body Γ (unary P.V (suc z) raw)))
    (typed : Nonempty (Derivation body Γ (windowAt P.W ctx result raw)))
    (held : Nonempty (Derivation body Γ (unary (scratchVertices P.cover s) vertices raw))) :
    Nonempty (Derivation body Γ (memberGraph vertices raw)) := by
  let goal : Formula α := memberGraph vertices raw
  apply programCases (selectedMeasure P.R) ![raw] goal
  intro β j Δ p keep m
  simp only [unaryInputsRename] at m
  have accepted := renameInto valid j Δ keep
  have scratch := renameInto held j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at accepted scratch
  have W := renameInto typed j Δ keep
  rw [windowRename] at W
  have below := renameInto earlier j Δ keep
  rw [ownBelowRename] at below
  let q := raw.relabel j
  let verts := vertices.relabel j
  let c := ctx.relabel j
  let r := result.relabel j
  have row : ParentRow P s body Δ q p verts c r := ⟨⟨accepted,m,scratch⟩, W, below⟩
  change Nonempty (Derivation body Δ ((memberGraph vertices raw).relabel j))
  rw [graphRename]
  exact step β Δ q p verts c r row

theorem allOwnFromBelow (P : Programs) (s : Settings) (raw : OTerm α)
    (step : PointOwnStep P s body)
    (earlier : Nonempty (Derivation body Γ (ownBelow P.V P.W P.cover s raw)))
    (valid : Nonempty (Derivation body Γ (unary P.V (suc z) raw))) :
    Nonempty (Derivation body Γ (ownAll P.W P.cover s raw)) := by
  let j : α → α ⊕ Fin 3 := Sum.inl
  let q := raw.relabel j
  let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let result : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let out : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let types := windowAt P.W c result q
  let held := unary (scratchVertices P.cover s) out q
  let D : List (Formula (α ⊕ Fin 3)) := Γ.map (fun f => f.relabel j)
  let E : List (Formula (α ⊕ Fin 3)) := held :: types :: D
  have keep : ∀ f ∈ Γ, f.relabel j ∈ E := by
    intro f hf
    exact List.mem_cons_of_mem held (List.mem_cons_of_mem types (List.mem_map.mpr ⟨f,hf,rfl⟩))
  have small := renameInto earlier j E keep
  rw [ownBelowRename] at small
  have accepted := renameInto valid j E keep
  simp only [unaryRename,sucRelabel,zRelabel] at accepted
  have W : Nonempty (Derivation body E types) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have installed : Nonempty (Derivation body E held) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hit⟩ := ownAtActualMeasuredPoint P s q out c result step small accepted W installed
  have matrix : Nonempty (Derivation body D (ownMatrix P.W P.cover s raw)) :=
    ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction hit)⟩
  exact actualFiniteUniversalIntroduction body α 3 Γ (ownMatrix P.W P.cover s raw) matrix

#print axioms ownAtActualMeasuredPoint
#print axioms allOwnFromBelow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedInductionPointProof
