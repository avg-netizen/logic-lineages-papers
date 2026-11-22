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

import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonRestrictedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePrefixedRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonChecks
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
open NumberedWindowInternalSparseMembersComparisonRestrictedProof (membersRename restricted)
open NumberedWindowInternalSparsePrefixedRoundsChecks (exact_RoundsInUpper)
open NumberedWindowInternalSparsePrefixedRoundsTargets (prefixed)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_PassInputsMonotone : ExactPassInputsMonotone := monotone
theorem exact_RestrictedMembersPrefixed : ExactRestrictedMembersPrefixed := restricted

private theorem roundIntoLarger (pred : ExactRetainedPredecessor) (E : Program 4)
    (va vb ctx ty seedA seedB a b size : OTerm α)
    (sub : Nonempty (Derivation body Γ (included va vb)))
    (initial : Nonempty (Derivation body Γ (memberGraph b seedA)))
    (left : Nonempty (Derivation body Γ (roundGraph E a size va ctx ty seedA)))
    (right : Nonempty (Derivation body Γ (membersGraph E b vb ctx ty seedB))) :
    Nonempty (Derivation body Γ (included a b)) := by
  apply programCases (pass E) (passTape va b ctx ty) _
  intro β j Θ later keep raw
  rw [includedRename]
  simp only [passTape,quadInputsRename] at raw
  have s := renameInto sub j Θ keep
  have k := renameInto initial j Θ keep
  have l := renameInto left j Θ keep
  have r := renameInto right j Θ keep
  rw [includedRename] at s
  rw [graphRename] at k
  rw [roundRename] at l
  rw [membersRename] at r
  obtain ⟨s⟩ := s
  obtain ⟨k⟩ := k
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := r
  obtain ⟨raw⟩ := raw
  obtain ⟨rest⟩ := restricted pred E body β Θ (va.relabel j) (vb.relabel j) (ctx.relabel j)
    (ty.relabel j) (seedB.relabel j) (b.relabel j) later
  have already := Derivation.implicationElimination rest (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction s r) raw)
  obtain ⟨rule⟩ := exact_RoundsInUpper pred E body β Θ (va.relabel j) (ctx.relabel j) (ty.relabel j)
    (seedA.relabel j) (b.relabel j) later (size.relabel j) (a.relabel j)
  exact ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction k (Derivation.conjunctionIntroduction raw already)) l)⟩

theorem exact_MembersSeedInclusion : ExactMembersSeedInclusion := by
  intro pred E body α Γ va vb ctx ty seedA seedB a b
  let A := (included va vb ⊓ memberGraph b seedA) ⊓
    (membersGraph E a va ctx ty seedA ⊓ membersGraph E b vb ctx ty seedB)
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have result : Nonempty (Derivation body Δ (included a b)) := by
    apply programCases poolLength ![va] _
    intro β j Θ size keep len
    rw [includedRename]
    rw [unaryInputsRename] at len
    have input := renameInto ⟨h⟩ j Θ keep
    simp only [A,conjunctionRename,includedRename,graphRename,membersRename] at input
    obtain ⟨input⟩ := input
    obtain ⟨len⟩ := len
    obtain ⟨law⟩ := exact_OpenMembersAtLength E body β Θ (a.relabel j) size (va.relabel j)
      (ctx.relabel j) (ty.relabel j) (seedA.relabel j)
    have runs := Derivation.conjunctionRight input
    have pair := Derivation.conjunctionLeft input
    have first := Derivation.implicationElimination (Derivation.conjunctionLeft
      (Derivation.implicationElimination law len)) (Derivation.conjunctionLeft runs)
    exact roundIntoLarger pred E (va.relabel j) (vb.relabel j) (ctx.relabel j) (ty.relabel j)
      (seedA.relabel j) (seedB.relabel j) (a.relabel j) (b.relabel j) size
      ⟨Derivation.conjunctionLeft pair⟩ ⟨Derivation.conjunctionRight pair⟩ ⟨first⟩
      ⟨Derivation.conjunctionRight runs⟩
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩

#print axioms exact_PassInputsMonotone
#print axioms exact_RestrictedMembersPrefixed
#print axioms exact_MembersSeedInclusion
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonChecks
