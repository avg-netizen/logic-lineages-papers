module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldImageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryExpansion.PreservationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryEdgeInclusion.AppendRightProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalListMap (mapHead)
open ID1Completion.InternalListMapProof (mapHeadValue)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue valueUnique headTransport)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn)
open ID1Completion.InternalTagArithmeticSupportProof (symm refl)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalCoverCartesianFoldTargets
open NumberedWindowInternalCoverCartesianFoldSyntaxProof
open NumberedWindowInternalCoverCartesianFoldImageProof (imageOfMember memberOfImage)

attribute [local irreducible] programGraph

variable {k : Nat} {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem moveInput (D : Program (k+1)) (head source out : OTerm α) (params : Fin k → OTerm α)
    (eq : Derivation body Γ (eqn head source))
    (run : Nonempty (Derivation body Γ (programGraph D out (Fin.cons head params)))) :
    Nonempty (Derivation body Γ (programGraph D out (Fin.cons source params))) := by
  unfold programGraph at run ⊢
  apply graphInputTransport body α (k+1) Γ _ out (Fin.cons head params) (Fin.cons source params) _ run
  intro i
  simp only [onEquality]
  exact Fin.cases (Nonempty.intro eq) (fun j => Nonempty.intro (refl (params j))) i

private theorem fromAppend (D : Program (k+1)) (raw head tail source deps image out block rest : OTerm α)
    (params : Fin k → OTerm α) (cell : Derivation body Γ (consGraph raw head tail))
    (sourceMember : Derivation body Γ (memberGraph raw source))
    (known : Derivation body Γ (programGraph D deps (Fin.cons source params)))
    (selected : Derivation body Γ (memberGraph deps image))
    (headBlock : Derivation body Γ (programGraph D block (Fin.cons head params)))
    (tailRun : Derivation body Γ (flatGraph D rest tail params))
    (appended : Derivation body Γ (programGraph append out ![block,rest]))
    (ih : Derivation body Γ (atList D tail source image params)) :
    Nonempty (Derivation body Γ (memberGraph out image)) := by
  obtain ⟨sum⟩ := consInversion raw head tail source ⟨cell⟩ ⟨sourceMember⟩
  let H := (missGraph head source).not
  let Tail := memberGraph tail source
  have hit : Derivation body (H :: Γ) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨same⟩ := nonzeroEquality head source hit
  have comparison := valueUnique D deps block (Fin.cons source params) ⟨addHyp known H⟩
    (moveInput D head source block params same ⟨addHyp headBlock H⟩)
  have headMember := headTransport scratchMember (suc z) deps block ![image] comparison ⟨addHyp selected H⟩
  obtain ⟨forward⟩ := PrimaryExpansion.PreservationProof.appendPreservation block rest out image
    ⟨addHyp appended H⟩ headMember
  have tailHit : Derivation body (Tail :: Γ) Tail := Derivation.hypothesis List.mem_cons_self
  have rightMember := memberOfImage D rest tail image params ⟨addHyp tailRun Tail⟩
    ⟨Derivation.implicationElimination (addHyp ih Tail) tailHit⟩
  obtain ⟨backward⟩ := PrimaryEdgeInclusion.AppendRightProof.appendPreservation block rest out image
    ⟨addHyp appended Tail⟩ rightMember
  exact ⟨disjunctionElimination sum (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

private theorem fromStep (D : Program (k+1)) (raw head tail source deps image out rest : OTerm α)
    (params : Fin k → OTerm α) (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (sourceMember : Nonempty (Derivation body Γ (memberGraph raw source)))
    (known : Nonempty (Derivation body Γ (programGraph D deps (Fin.cons source params))))
    (selected : Nonempty (Derivation body Γ (memberGraph deps image)))
    (step : Nonempty (Derivation body Γ (programGraph (flatStep D) out (Fin.cons head (Fin.cons rest params)))))
    (tailRun : Nonempty (Derivation body Γ (flatGraph D rest tail params)))
    (ih : Nonempty (Derivation body Γ (atList D tail source image params))) :
    Nonempty (Derivation body Γ (memberGraph out image)) := by
  apply programCases D (Fin.cons head params) _
  intro β j Δ block keep headRun
  rw [graphRename]
  simp only [consTermRename] at headRun
  have cell' := renameInto cell j Δ keep
  have source' := renameInto sourceMember j Δ keep
  have known' := renameInto known j Δ keep
  have selected' := renameInto selected j Δ keep
  have step' := renameInto step j Δ keep
  have tail' := renameInto tailRun j Δ keep
  have ih' := renameInto ih j Δ keep
  simp only [consGraphRename] at cell'
  simp only [graphRename] at source' selected'
  simp only [programRename,consTermRename] at known' step'
  simp only [flatRename] at tail'
  simp only [atListRename] at ih'
  let ps := fun i => (params i).relabel j
  let xs := Fin.cons (head.relabel j) (Fin.cons (rest.relabel j) ps)
  have left := mapHeadValue D (head.relabel j) (rest.relabel j) block ps headRun
  have extract : Nonempty (Derivation body Δ (programGraph append (out.relabel j) ![block,rest.relabel j])) := by
    apply compositionRecover append ![mapHead D,.projection 1] (out.relabel j) xs ![block,rest.relabel j] step'
    intro i
    exact Fin.cases left (Fin.cases (projectionValue 1 xs) (fun n => Fin.elim0 n)) i
  obtain ⟨hc⟩ := cell'
  obtain ⟨hm⟩ := source'
  obtain ⟨hd⟩ := known'
  obtain ⟨hy⟩ := selected'
  obtain ⟨hh⟩ := headRun
  obtain ⟨ht⟩ := tail'
  obtain ⟨ha⟩ := extract
  obtain ⟨hi⟩ := ih'
  exact fromAppend D (raw.relabel j) (head.relabel j) (tail.relabel j) (source.relabel j)
    (deps.relabel j) (image.relabel j) (out.relabel j) block (rest.relabel j) ps hc hm hd hy hh ht ha hi

theorem onCons (D : Program (k+1)) (raw head tail source deps image out : OTerm α) (params : Fin k → OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph raw head tail)))
    (sourceMember : Nonempty (Derivation body Γ (memberGraph raw source)))
    (known : Nonempty (Derivation body Γ (programGraph D deps (Fin.cons source params))))
    (selected : Nonempty (Derivation body Γ (memberGraph deps image)))
    (run : Nonempty (Derivation body Γ (flatGraph D out raw params)))
    (ih : Nonempty (Derivation body Γ (atList D tail source image params))) :
    Nonempty (Derivation body Γ (memberGraph out image)) := by
  have step := consForward (constantZero k) (flatStep D) raw head tail out params cell run
  apply stepCases (constantZero k) (flatStep D) out head tail params _ step
  intro β j Δ rest keep tailRun rowRun
  simp only [graphRename]
  simp only [consTermRename] at tailRun rowRun
  have cell' := renameInto cell j Δ keep
  have source' := renameInto sourceMember j Δ keep
  have known' := renameInto known j Δ keep
  have selected' := renameInto selected j Δ keep
  have ih' := renameInto ih j Δ keep
  simp only [consGraphRename] at cell'
  simp only [graphRename] at source' selected'
  simp only [programRename,consTermRename] at known'
  simp only [atListRename] at ih'
  exact fromStep D (raw.relabel j) (head.relabel j) (tail.relabel j) (source.relabel j)
    (deps.relabel j) (image.relabel j) (out.relabel j) rest (fun i => (params i).relabel j)
    cell' source' known' selected' rowRun tailRun ih'

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCartesianFoldStepProof
