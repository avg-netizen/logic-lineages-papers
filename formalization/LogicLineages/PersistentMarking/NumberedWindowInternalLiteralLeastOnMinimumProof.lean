module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseSeedOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRetainedScanChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalOrderSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMinimumProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMembersProof
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparseSeedOriginChecks (exact_RoundSeedOrigin)
open NumberedWindowInternalSparseRetainedScanChecks (exact_RetainedPredecessor)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseScratchMembershipOpenChecks (exact_OpenScratchMinimumOccurs)
open NumberedWindowInternalSparseMinimumBoundChecks (exact_OpenScratchMinimumLowerBound)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Open the actual scratch minimum using a held packed success and
the physical output of its member program. A rejected parser would
give zero, contradicting the observed successor. -/
theorem exact_OpenLeastOnMinimum (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed pool m : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty seed m))
    (pooled : D B Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed])) :
    D B Γ (unary scratchMinimum (suc m) pool) := by
  apply optionGraphCases contextOption ![ctx,ty,seed] _
  · intro β j Δ keep zero
    rw [unaryRename,sucRelabel]
    rw [tripleInputsRename] at zero
    have h := renameInto actual j Δ keep
    rw [leastOnRename] at h
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have absent := zeroBranchElim contextOption (constantZero 3) (minimumAtMembersOn C E s)
      (suc (m.relabel j)) xs zero h
    obtain ⟨no⟩ := valueUnique (constantZero 3) (suc (m.relabel j)) z xs absent (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply no)⟩
  · intro β j Δ payload keep parsed
    rw [unaryRename,sucRelabel]
    rw [tripleInputsRename] at parsed
    have h := renameInto actual j Δ keep
    rw [leastOnRename] at h
    have pp := renameInto pooled j Δ keep
    simp only [programRename,tripleInputsRename] at pp
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have branch := successorBranchElim contextOption (constantZero 3) (minimumAtMembersOn C E s)
      (suc (m.relabel j)) payload xs parsed h
    apply compositionRecover scratchMinimum (fun _ : Fin 1 => membersAtSeedOn C E s)
      (suc (m.relabel j)) xs ![pool.relabel j] branch
    intro i
    obtain rfl := Fin.eq_zero i
    exact pp

theorem exact_OpenLeastOnSelected (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed pool m : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty seed m))
    (pooled : D B Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed])) :
    D B Γ (memberGraph pool m) := by
  obtain ⟨run⟩ := exact_OpenLeastOnMinimum C E s ctx ty seed pool m actual pooled
  obtain ⟨occurs⟩ := exact_OpenScratchMinimumOccurs B α Γ pool m
  exact ⟨Derivation.implicationElimination occurs run⟩

theorem exact_OpenLeastOnLower (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed pool candidate m : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty seed m))
    (pooled : D B Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed]))
    (candidateIn : D B Γ (memberGraph pool candidate)) :
    D B Γ (ltF candidate m).not := by
  obtain ⟨run⟩ := exact_OpenLeastOnMinimum C E s ctx ty seed pool m actual pooled
  obtain ⟨candidateIn⟩ := candidateIn
  obtain ⟨bound⟩ := exact_OpenScratchMinimumLowerBound B α Γ pool candidate m
  exact ⟨Derivation.implicationElimination bound (Derivation.conjunctionIntroduction run candidateIn)⟩

/-- Any actual successful selected minimum witnesses the original seed
in the particular scratch cover used by its actual round report. -/
theorem exact_OpenLeastOnSeedOrigin (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed vertices pool m : OTerm α)
    (actual : D B Γ (leastOnGraph C E s ctx ty seed m))
    (pooled : D B Γ (programGraph (membersAtSeedOn C E s) pool ![ctx,ty,seed]))
    (cover : D B Γ (unary (scratchVertices C s) vertices seed)) :
    D B Γ (memberGraph vertices seed) := by
  have selected := exact_OpenLeastOnSelected C E s ctx ty seed pool m actual pooled
  have rounds := exact_OpenLeastOnActualMembers C E s ctx ty seed vertices pool cover pooled
  apply programCases poolLength ![vertices] _
  intro β j Δ fuel keep length
  rw [graphRename]
  rw [unaryInputsRename] at length
  have occ := renameInto selected j Δ keep
  rw [graphRename] at occ
  have rs := renameInto rounds j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at rs
  obtain ⟨len⟩ := length
  obtain ⟨os⟩ := occ
  obtain ⟨rs⟩ := rs
  obtain ⟨tape⟩ := exact_OpenMembersAtLength E B β Δ (pool.relabel j) fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
  have run := Derivation.implicationElimination (Derivation.conjunctionLeft
    (Derivation.implicationElimination tape len)) rs
  obtain ⟨origin⟩ := exact_RoundSeedOrigin exact_RetainedPredecessor E B β Δ fuel
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (pool.relabel j) (m.relabel j)
  exact ⟨Derivation.implicationElimination origin (Derivation.conjunctionIntroduction run os)⟩

#print axioms exact_OpenLeastOnMinimum
#print axioms exact_OpenLeastOnSelected
#print axioms exact_OpenLeastOnLower
#print axioms exact_OpenLeastOnSeedOrigin
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnMinimumProof
