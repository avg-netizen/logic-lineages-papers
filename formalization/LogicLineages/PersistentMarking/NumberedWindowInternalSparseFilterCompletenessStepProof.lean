module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterRetentionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionCompositionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalListCodecSupportProof (consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (pass passGraph cell)
open NumberedWindowInternalSparseDirectedSeen (scanGraph)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph hitGraph hitRename)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseFilterInclusionCompositionProof (hitIntro hitCases)
open NumberedWindowInternalSparseRoundWindowSingletonProof (nonzeroEquality)
open NumberedWindowInternalSparseFilterRetentionChecks (exact_ScannedHeadRetained exact_FilteredTailRetained)
open NumberedWindowInternalSparseFilterCompletenessSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem tailHit (E : Program 4) (n h t seen ctx ty k out : OTerm α)
    (c : Nonempty (Derivation body Γ (cell n h t))) (r : Nonempty (Derivation body Γ (passGraph E out n seen ctx ty)))
    (tail : Nonempty (Derivation body Γ (hitGraph E t seen ctx ty k))) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  apply hitCases E t seen ctx ty k _ tail
  intro β j Δ rest keep passTail member
  rw [graphRename]
  have c' := renameInto c j Δ keep
  change Nonempty (Derivation body Δ ((ID1Completion.InternalListCodecSupportProof.consGraph n h t).relabel j)) at c'
  rw [consGraphRename] at c'
  have r' := renameInto r j Δ keep
  rw [passRename] at r'
  obtain ⟨law⟩ := exact_FilteredTailRetained E body β Δ (n.relabel j) (h.relabel j) (t.relabel j)
    (seen.relabel j) (ctx.relabel j) (ty.relabel j) (out.relabel j) rest (k.relabel j)
  obtain ⟨c'⟩ := c'
  obtain ⟨r'⟩ := r'
  obtain ⟨p⟩ := passTail
  obtain ⟨m⟩ := member
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction c' r') (Derivation.conjunctionIntroduction p m))⟩

private theorem eachOutput (E : Program 4) (n h t seen ctx ty k out : OTerm α)
    (c : Derivation body Γ (cell n h t)) (run : Derivation body Γ (passGraph E out n seen ctx ty))
    (ih : Derivation body Γ (completeAt E t seen ctx ty k))
    (m : Derivation body Γ (memberGraph n k)) (g : Derivation body Γ (scanGraph E seen ctx ty k)) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  obtain ⟨split⟩ := consInversion n h t k ⟨c⟩ ⟨m⟩
  let L := (missGraph h k).not
  let R := memberGraph t k
  have l : Derivation body (L :: Γ) L := Derivation.hypothesis List.mem_cons_self
  obtain ⟨same⟩ := nonzeroEquality h k l
  let S := scanGraph E seen ctx ty h
  obtain ⟨retain⟩ := exact_ScannedHeadRetained E body α (S :: L :: Γ) n h t seen ctx ty out
  have useHead := Derivation.implicationElimination retain (Derivation.conjunctionIntroduction
    (addHyp (addHyp (Derivation.conjunctionIntroduction c run) L) S) (Derivation.hypothesis List.mem_cons_self))
  obtain ⟨byK⟩ := moveHead E out seen ctx ty h k same (Derivation.implicationIntroduction useHead)
  have left := Derivation.implicationElimination byK (addHyp g L)
  have r : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  have rest := Derivation.implicationElimination (addHyp ih R) (Derivation.conjunctionIntroduction r (addHyp g R))
  obtain ⟨right⟩ := tailHit E n h t seen ctx ty k out ⟨addHyp c R⟩ ⟨addHyp run R⟩ ⟨rest⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩

theorem atCons (E : Program 4) (n h t seen ctx ty k : OTerm α)
    (cellDer : Nonempty (Derivation body Γ (cell n h t))) (tail : Nonempty (Derivation body Γ (completeAt E t seen ctx ty k))) :
    Nonempty (Derivation body Γ (completeAt E n seen ctx ty k)) := by
  let A := memberGraph n k ⊓ scanGraph E seen ctx ty k
  let Δ := A :: Γ
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨c⟩ := cellDer
  obtain ⟨ih⟩ := tail
  have output : Nonempty (Derivation body Δ (hitGraph E n seen ctx ty k)) := by
    apply programCases (pass E) ![n,seen,ctx,ty] _
    intro β j Θ out keep run
    rw [hitRename]
    rw [quadInputsRename] at run
    have cj := renameInto ⟨addHyp c A⟩ j Θ keep
    change Nonempty (Derivation body Θ ((ID1Completion.InternalListCodecSupportProof.consGraph n h t).relabel j)) at cj
    rw [consGraphRename] at cj
    have old := renameInto ⟨addHyp ih A⟩ j Θ keep
    rw [completeRename] at old
    have m := renameInto ⟨Derivation.conjunctionLeft input⟩ j Θ keep
    rw [graphRename] at m
    have g := renameInto ⟨Derivation.conjunctionRight input⟩ j Θ keep
    rw [scanRename] at g
    obtain ⟨cj⟩ := cj
    obtain ⟨old⟩ := old
    obtain ⟨m⟩ := m
    obtain ⟨g⟩ := g
    obtain ⟨p⟩ := run
    exact hitIntro E out _ _ _ _ _ ⟨p⟩ (eachOutput E _ _ _ _ _ _ _ out cj p old m g)
  obtain ⟨d⟩ := output
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessStepProof
