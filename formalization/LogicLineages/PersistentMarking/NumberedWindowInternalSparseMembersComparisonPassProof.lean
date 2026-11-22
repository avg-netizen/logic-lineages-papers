module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundStabilityChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScanWitnessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterCompletenessChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryMonotonicity.InclusionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonPassProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourceComputabilityCompletion.Continuation20261114
open PrimaryMonotonicity (included)
open PrimaryMonotonicity.InclusionProof (includedRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDirectedFilter (passGraph)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseDirectedSeen (scanGraph seenWitness witnessRow)
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (witnessUnfold witnessBinder scanRename)
open NumberedWindowInternalSparseScanWitnessChecks (exact_WitnessRowAcceptance exact_OpenScanWitnessEquivalence)
open NumberedWindowInternalSparseFilterInclusionChecks (exact_DirectedPassInclusion)
open NumberedWindowInternalSparseFilterCompletenessChecks (exact_ScannedMemberRetention)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenRoundSuccessor)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalSparseMembersComparisonTargets
open NumberedWindowInternalSparseRoundStabilityChecks (exact_ScanMonotonicity)
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem monotone : ExactPassInputsMonotone := by
  intro paid E body α Γ va vb left right ctx ty a b
  let runs := passGraph E a va left ctx ty ⊓ passGraph E b vb right ctx ty
  let A := (included va vb ⊓ included left right) ⊓ runs
  let Δ := A :: Γ
  have h : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have rr := Derivation.conjunctionRight h
  have grow : Nonempty (Derivation body Δ (included a b)) := by
    apply PrimaryMonotonicity.InclusionProof.introduce
    intro β j Θ k keep hit
    have i := renameInto ⟨Derivation.conjunctionRight (Derivation.conjunctionLeft h)⟩ j Θ keep
    have vi := renameInto ⟨Derivation.conjunctionLeft (Derivation.conjunctionLeft h)⟩ j Θ keep
    have l := renameInto ⟨Derivation.conjunctionLeft rr⟩ j Θ keep
    have r := renameInto ⟨Derivation.conjunctionRight rr⟩ j Θ keep
    rw [includedRename] at i vi
    rw [passRename] at l r
    obtain ⟨l⟩ := l
    obtain ⟨r⟩ := r
    obtain ⟨hit⟩ := hit
    have m : Derivation body Θ (memberGraph (a.relabel j) k) := hit
    have given := Derivation.conjunctionIntroduction l m
    obtain ⟨origin⟩ := exact_DirectedPassInclusion E body β Θ (a.relabel j) (va.relabel j)
      (left.relabel j) (ctx.relabel j) (ty.relabel j) k
    obtain ⟨prior⟩ := paid E body β Θ (va.relabel j) (left.relabel j) (ctx.relabel j)
      (ty.relabel j) (a.relabel j) k
    obtain ⟨both⟩ := exact_OpenScanWitnessEquivalence E body β Θ (left.relabel j) (ctx.relabel j) (ty.relabel j) k
    have scan := Derivation.implicationElimination (Derivation.conjunctionRight both)
      (Derivation.implicationElimination prior given)
    obtain ⟨changeSeen⟩ := exact_ScanMonotonicity E body β Θ (left.relabel j) (right.relabel j)
      (ctx.relabel j) (ty.relabel j) k
    obtain ⟨i⟩ := i
    have test := Derivation.implicationElimination changeSeen (Derivation.conjunctionIntroduction i scan)
    obtain ⟨vertex⟩ := PrimaryMonotonicity.InclusionProof.eliminate (va.relabel j) (vb.relabel j) k
      vi ⟨Derivation.implicationElimination origin given⟩
    obtain ⟨insert⟩ := exact_ScannedMemberRetention E body β Θ (b.relabel j) (vb.relabel j)
      (right.relabel j) (ctx.relabel j) (ty.relabel j) k
    exact ⟨Derivation.implicationElimination insert (Derivation.conjunctionIntroduction r
      (Derivation.conjunctionIntroduction vertex test))⟩
  obtain ⟨grow⟩ := grow
  exact ⟨Derivation.implicationIntroduction grow⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMembersComparisonPassProof
