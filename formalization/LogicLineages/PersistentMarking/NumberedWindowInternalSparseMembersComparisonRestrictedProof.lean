module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonPassProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersClosureChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonRestrictedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryMonotonicity (included)
open PrimaryMonotonicity.InclusionProof (includedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (pass passGraph passTape)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseMembersComparisonTargets
open NumberedWindowInternalSparseMembersComparisonPassProof (monotone)
open NumberedWindowInternalSparseMembersClosureChecks (exact_LengthStableFromPredecessor)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength exact_OpenRoundSuccessor)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem membersRename (E : Program 4) (pool vertices ctx ty seed : OTerm α) {β : Type} (j : α → β) :
    (membersGraph E pool vertices ctx ty seed).relabel j =
      membersGraph E (pool.relabel j) (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) := by
  simp only [membersGraph,programRename,membersTape,quadInputsRename]

private theorem fullPass (pred : ExactRetainedPredecessor) (E : Program 4) (v ctx ty seed pool later : OTerm α)
    (m : Nonempty (Derivation body Γ (membersGraph E pool v ctx ty seed)))
    (p : Nonempty (Derivation body Γ (passGraph E later v pool ctx ty))) :
    Nonempty (Derivation body Γ (included later pool)) := by
  apply programCases poolLength ![v] _
  intro β j Θ size keep len
  rw [includedRename]
  rw [unaryInputsRename] at len
  have member := renameInto m j Θ keep
  have passOut := renameInto p j Θ keep
  rw [membersRename] at member
  rw [passRename] at passOut
  obtain ⟨member⟩ := member
  obtain ⟨passOut⟩ := passOut
  obtain ⟨len⟩ := len
  obtain ⟨atLength⟩ := exact_OpenMembersAtLength E body β Θ (pool.relabel j) size
    (v.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have here := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination atLength len)) member
  obtain ⟨succ⟩ := exact_OpenRoundSuccessor E body β Θ (later.relabel j) size (v.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) (pool.relabel j)
  have next := Derivation.implicationElimination (Derivation.conjunctionRight
    (Derivation.implicationElimination succ here)) passOut
  obtain ⟨stable⟩ := exact_LengthStableFromPredecessor pred E body β Θ (v.relabel j)
    (ctx.relabel j) (ty.relabel j) (seed.relabel j) size (pool.relabel j) (later.relabel j)
  exact ⟨Derivation.implicationElimination stable (Derivation.conjunctionIntroduction len
    (Derivation.conjunctionIntroduction here next))⟩

private theorem transitive (a b c : OTerm α)
    (ab : Nonempty (Derivation body Γ (included a b))) (bc : Nonempty (Derivation body Γ (included b c))) :
    Nonempty (Derivation body Γ (included a c)) := by
  apply PrimaryMonotonicity.InclusionProof.introduce
  intro β j Θ k keep hit
  have first := renameInto ab j Θ keep
  have second := renameInto bc j Θ keep
  rw [includedRename] at first second
  exact PrimaryMonotonicity.InclusionProof.eliminate _ _ k second
    (PrimaryMonotonicity.InclusionProof.eliminate _ _ k first hit)

theorem restricted : ExactRestrictedMembersPrefixed := by
  intro pred E body α Γ va vb ctx ty seed pool later
  let A := (included va vb ⊓ membersGraph E pool vb ctx ty seed) ⊓ passGraph E later va pool ctx ty
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have result : Nonempty (Derivation body Δ (included later pool)) := by
    apply programCases (pass E) (passTape vb pool ctx ty) _
    intro β j Θ full keep run
    rw [includedRename]
    simp only [passTape,quadInputsRename] at run
    obtain ⟨run⟩ := run
    have input := renameInto ⟨h⟩ j Θ keep
    simp only [A,conjunctionRename,includedRename,membersRename,passRename] at input
    obtain ⟨input⟩ := input
    have inc := Derivation.conjunctionLeft (Derivation.conjunctionLeft input)
    have member := Derivation.conjunctionRight (Derivation.conjunctionLeft input)
    have refl : Nonempty (Derivation body Θ (included (pool.relabel j) (pool.relabel j))) :=
      PrimaryMonotonicity.InclusionProof.introduce _ _ (fun _ _ _ _ _ hit => hit)
    obtain ⟨refl⟩ := refl
    obtain ⟨mono⟩ := monotone pred E body β Θ (va.relabel j) (vb.relabel j) (pool.relabel j)
      (pool.relabel j) (ctx.relabel j) (ty.relabel j) (later.relabel j) full
    have small := Derivation.implicationElimination mono (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction inc refl) (Derivation.conjunctionIntroduction
        (Derivation.conjunctionRight input) run))
    exact transitive _ full _ ⟨small⟩ (fullPass pred E (vb.relabel j) (ctx.relabel j)
      (ty.relabel j) (seed.relabel j) (pool.relabel j) full ⟨member⟩ ⟨run⟩)
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonRestrictedProof
