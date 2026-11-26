module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAppendInclusionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverArgumentCellsTransportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAppendInclusionProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph appears)
open NumberedWindowInternalScratchAppendOpenChecks (fromLeft fromRight)
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalCoverArgumentCellsTargets (axisInclusion)
open NumberedWindowInternalCoverArgumentCellsTransportProof (axisRename)
open NumberedWindowInternalCoverAppendInclusionTargets

private theorem atKey {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (old next key : OTerm α)
    (all : Nonempty (Derivation body Γ (axisInclusion old next)))
    (member : Derivation body Γ (memberGraph old key)) :
    Nonempty (Derivation body Γ (memberGraph next key)) := by
  obtain ⟨d⟩ := all
  have selected := Derivation.universalElimination (emb key) d
  have step : Derivation body Γ ((memberGraph old key).imp (memberGraph next key)) := by
    simpa only [instantiate,bindEmbedding,impSubst,memberSubst,liftBind,varBind] using selected
  exact ⟨Derivation.implicationElimination step member⟩

private theorem appendKey {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (left right leftNext rightNext out outNext key : OTerm α)
    (old : Nonempty (Derivation body Γ (appendGraph out left right)))
    (next : Nonempty (Derivation body Γ (appendGraph outNext leftNext rightNext)))
    (hl : Nonempty (Derivation body Γ (axisInclusion left leftNext)))
    (hr : Nonempty (Derivation body Γ (axisInclusion right rightNext)))
    (hit : Nonempty (Derivation body Γ (memberGraph out key))) :
    Nonempty (Derivation body Γ (memberGraph outNext key)) := by
  obtain ⟨which⟩ := exact_OpenScratchAppendOrigin body α Γ left right out key old hit
  let L := memberGraph left key
  let R := memberGraph right key
  obtain ⟨lm⟩ := atKey (Γ := L :: Γ) left leftNext key (withHyp hl L)
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨rm⟩ := atKey (Γ := R :: Γ) right rightNext key (withHyp hr R)
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨ll⟩ := fromLeft leftNext rightNext outNext key (withHyp next L) ⟨lm⟩
  obtain ⟨rr⟩ := fromRight leftNext rightNext outNext key (withHyp next R) ⟨rm⟩
  exact ⟨disjunctionElimination which (Derivation.implicationIntroduction ll)
    (Derivation.implicationIntroduction rr)⟩

theorem exact_OpenOriginalAppendInclusion : ExactOpenOriginalAppendInclusion := by
  intro body α Γ left right leftNext rightNext out outNext old next hl hr
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let M := memberGraph (out.relabel j) key
  let Δ := M :: Γ.map (fun q => q.relabel j)
  have keep : ∀ q ∈ Γ, q.relabel j ∈ Δ := by
    intro q h
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,h,rfl⟩)
  have old' := renameInto old j Δ keep
  have next' := renameInto next j Δ keep
  have hl' := renameInto hl j Δ keep
  have hr' := renameInto hr j Δ keep
  simp only [appendGraph,programRename,binaryInputsRename] at old' next'
  rw [axisRename] at hl' hr'
  obtain ⟨result⟩ := appendKey (Γ := Δ) (left.relabel j) (right.relabel j)
    (leftNext.relabel j) (rightNext.relabel j) (out.relabel j) (outNext.relabel j) key
    old' next' hl' hr' ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

#print axioms exact_OpenOriginalAppendInclusion

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAppendInclusionProof
