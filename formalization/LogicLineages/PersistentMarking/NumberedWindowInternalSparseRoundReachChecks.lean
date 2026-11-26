module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundsInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenRoundZero exact_OpenRoundSuccessor)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseRoundsInclusionTargets (RoundsIncluded)
open NumberedWindowInternalSparseRoundsInclusionChecks (exact_RoundsInclusionFromPass)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalSparseFilterCompletenessChecks (exact_ScannedMemberRetention)
open NumberedWindowInternalSparseScanWitnessChecks (exact_WitnessRowAcceptance)
open NumberedWindowInternalSparseRoundReachTargets
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem included (E : Program 4) : RoundsIncluded E :=
  (exact_RoundsInclusionFromPass E (exact_DirectedPassInclusion (constantZero 4)) (exact_DirectedPassInclusion E)).1

private theorem enter (E : Program 4) (out vertices seen ctx ty w k : OTerm α)
    (run : Derivation body Γ (passGraph E out vertices seen ctx ty))
    (vertex : Derivation body Γ (memberGraph vertices k)) (old : Derivation body Γ (memberGraph seen w))
    (reach : Derivation body Γ (eqn w k ⊔ acceptEdge E ctx ty w k)) :
    Nonempty (Derivation body Γ (memberGraph out k)) := by
  obtain ⟨tested⟩ := exact_WitnessRowAcceptance E body α Γ seen ctx ty w k
  have scan := Derivation.implicationElimination tested (Derivation.conjunctionIntroduction old reach)
  obtain ⟨retained⟩ := exact_ScannedMemberRetention E body α Γ out vertices seen ctx ty k
  exact ⟨Derivation.implicationElimination retained (Derivation.conjunctionIntroduction run
    (Derivation.conjunctionIntroduction vertex scan))⟩

private theorem start (E : Program 4) (out vertices ctx ty seed : OTerm α)
    (round : Nonempty (Derivation body Γ (roundGraph E out z vertices ctx ty seed)))
    (vertex : Nonempty (Derivation body Γ (memberGraph vertices seed))) :
    Nonempty (Derivation body Γ (memberGraph out seed)) := by
  apply programCases consCode ![seed,z] _
  intro β j Δ singleton keep cell
  rw [binaryInputsRename,zRelabel] at cell
  rw [graphRename]
  have r := renameInto round j Δ keep
  rw [roundRename,zRelabel] at r
  have v := renameInto vertex j Δ keep
  rw [graphRename] at v
  obtain ⟨head⟩ := headMember (body := body) (Γ := Δ) singleton (seed.relabel j) z (seed.relabel j) cell ⟨refl _⟩
  obtain ⟨rule⟩ := exact_OpenRoundZero E body β Δ (out.relabel j) (vertices.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) singleton
  obtain ⟨cell⟩ := cell
  obtain ⟨r⟩ := r
  obtain ⟨v⟩ := v
  have filtered := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination rule cell)) r
  exact enter (constantZero 4) _ _ _ _ _ _ _ filtered v head (orLeft (refl _))

theorem exact_SeedRoundZero : ExactSeedRoundZero := by
  intro E body α Γ out vertices ctx ty seed
  let R := roundGraph E out z vertices ctx ty seed
  let A := memberGraph vertices seed
  let B := memberGraph out seed
  have r : Derivation body (R :: Γ) R := Derivation.hypothesis List.mem_cons_self
  obtain ⟨yes⟩ := start (Γ := A :: R :: Γ) E out vertices ctx ty seed ⟨addHyp r A⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨law⟩ := included E body α (B :: R :: Γ) out z vertices ctx ty seed seed
  have back := Derivation.implicationElimination law (Derivation.conjunctionIntroduction (addHyp r B)
    (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction yes) (Derivation.implicationIntroduction back))⟩

private theorem successor (E : Program 4) (before after fuel vertices ctx ty seed w k : OTerm α)
    (stages : Derivation body Γ (roundGraph E before fuel vertices ctx ty seed ⊓
      roundGraph E after (suc fuel) vertices ctx ty seed))
    (vertex : Derivation body Γ (memberGraph vertices k)) (old : Derivation body Γ (memberGraph before w))
    (reach : Derivation body Γ (eqn w k ⊔ acceptEdge E ctx ty w k)) :
    Nonempty (Derivation body Γ (memberGraph after k)) := by
  obtain ⟨rule⟩ := exact_OpenRoundSuccessor E body α Γ after fuel vertices ctx ty seed before
  have pass := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination rule (Derivation.conjunctionLeft stages))) (Derivation.conjunctionRight stages)
  exact enter E _ _ _ _ _ _ _ pass vertex old reach

theorem exact_RoundEdgeExtension : ExactRoundEdgeExtension := by
  intro E body α Γ before after fuel vertices ctx ty seed w k
  let stages := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let A := stages ⊓ ((memberGraph before w ⊓ acceptEdge E ctx ty w k) ⊓ memberGraph vertices k)
  have a : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have data := Derivation.conjunctionRight a
  have prev := Derivation.conjunctionLeft data
  obtain ⟨d⟩ := successor E _ _ _ _ _ _ _ w k (Derivation.conjunctionLeft a)
    (Derivation.conjunctionRight data) (Derivation.conjunctionLeft prev) (orRight (Derivation.conjunctionRight prev))
  exact ⟨Derivation.implicationIntroduction d⟩

theorem exact_AdjacentRoundPersistence : ExactAdjacentRoundPersistence := by
  intro E body α Γ before after fuel vertices ctx ty seed k
  let stages := roundGraph E before fuel vertices ctx ty seed ⊓ roundGraph E after (suc fuel) vertices ctx ty seed
  let A := stages ⊓ memberGraph before k
  have a : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have prior := Derivation.conjunctionLeft a
  have old := Derivation.conjunctionRight a
  obtain ⟨inc⟩ := included E body α (A :: Γ) before fuel vertices ctx ty seed k
  have vertex := Derivation.implicationElimination inc (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft prior) old)
  obtain ⟨d⟩ := successor E _ _ _ _ _ _ _ k k prior vertex old (orLeft (refl k))
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_SeedRoundZero
#print axioms exact_RoundEdgeExtension
#print axioms exact_AdjacentRoundPersistence
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundReachChecks
