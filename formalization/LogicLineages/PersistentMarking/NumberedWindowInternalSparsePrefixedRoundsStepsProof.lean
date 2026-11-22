module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundStabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundOriginWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsStepsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryMonotonicity (included)
open PrimaryMonotonicity.InclusionProof (includedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseRoundOriginChecks (exact_ZeroRoundOrigin)
open NumberedWindowInternalSparseRoundOriginWitnessProof (moveMember)
open NumberedWindowInternalSparseRoundStabilityChecks (exact_PassMonotonicity)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenRoundSuccessor)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePrefixedRoundsTargets

theorem prefixedRename {α β : Type} (E : Program 4) (vertices ctx ty upper later : OTerm α) (j : α → β) :
    (prefixed E vertices ctx ty upper later).relabel j =
      prefixed E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (upper.relabel j) (later.relabel j) := by
  simp only [prefixed,conjunctionRename,passRename,includedRename]

theorem initial : ExactInitialInUpper := by
  intro pred E body α Γ vertices ctx ty seed upper out
  let A := roundGraph E out z vertices ctx ty seed ⊓ memberGraph upper seed
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have inc : Nonempty (Derivation body Δ (included out upper)) := by
    apply PrimaryMonotonicity.InclusionProof.introduce
    intro β j Θ k keep hit
    have d := renameInto ⟨h⟩ j Θ keep
    simp only [A,conjunctionRename,roundRename,zRelabel,graphRename] at d
    obtain ⟨d⟩ := d
    obtain ⟨hit⟩ := hit
    obtain ⟨origin⟩ := exact_ZeroRoundOrigin pred E body β Θ (out.relabel j) (vertices.relabel j)
      (ctx.relabel j) (ty.relabel j) (seed.relabel j) k
    have atom := Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination origin (Derivation.conjunctionLeft d))) hit
    exact moveMember (upper.relabel j) (seed.relabel j) k (Derivation.conjunctionRight atom)
      (Derivation.conjunctionRight d)
  obtain ⟨inc⟩ := inc
  exact ⟨Derivation.implicationIntroduction inc⟩

private theorem inclusionTrans {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (a b c : OTerm α) (ab : Nonempty (Derivation body Γ (included a b)))
    (bc : Nonempty (Derivation body Γ (included b c))) : Nonempty (Derivation body Γ (included a c)) := by
  apply PrimaryMonotonicity.InclusionProof.introduce
  intro β j Θ k keep hit
  have first := renameInto ab j Θ keep
  have second := renameInto bc j Θ keep
  rw [includedRename] at first second
  exact PrimaryMonotonicity.InclusionProof.eliminate _ _ k second
    (PrimaryMonotonicity.InclusionProof.eliminate _ _ k first hit)

theorem step : ExactStepInUpper := by
  intro pred E body α Γ vertices ctx ty seed upper later i before after
  let runs := roundGraph E before i vertices ctx ty seed ⊓ roundGraph E after (suc i) vertices ctx ty seed
  let A := prefixed E vertices ctx ty upper later ⊓ (runs ⊓ included before upper)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have pre := Derivation.conjunctionLeft h
  have both := Derivation.conjunctionRight h
  have pair := Derivation.conjunctionLeft both
  obtain ⟨round⟩ := exact_OpenRoundSuccessor E body α Δ after i vertices ctx ty seed before
  have current := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination round (Derivation.conjunctionLeft pair))) (Derivation.conjunctionRight pair)
  obtain ⟨mono⟩ := exact_PassMonotonicity pred E body α Δ vertices before upper ctx ty after later
  have subset := Derivation.implicationElimination mono
    (Derivation.conjunctionIntroduction (Derivation.conjunctionRight both)
      (Derivation.conjunctionIntroduction current (Derivation.conjunctionLeft pre)))
  obtain ⟨done⟩ := inclusionTrans after later upper ⟨subset⟩ ⟨Derivation.conjunctionRight pre⟩
  exact ⟨Derivation.implicationIntroduction done⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsStepsProof
