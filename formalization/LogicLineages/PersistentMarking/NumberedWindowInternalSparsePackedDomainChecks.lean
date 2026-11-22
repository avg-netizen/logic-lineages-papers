module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedSeedPresenceChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (enter hasRename casesLeast)
open NumberedWindowInternalSparseMinimumBoundWitnessProof (casesValue)
open NumberedWindowInternalSparsePackedDomainTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)

theorem exact_SeedInComputedPool : ExactSeedInComputedPool :=
  NumberedWindowInternalSparsePackedDomainMemberProof.seedInComputedPool

private theorem fromMember (ctx ty seed payload pool : OTerm α)
    (parsed : Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (computed : Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed])))
    (hit : Nonempty (Derivation body Γ (memberGraph pool seed))) :
    Nonempty (Derivation body Γ (hasLeast C X W s ctx ty seed)) := by
  obtain ⟨existsMin⟩ := NumberedWindowInternalSparseMinimumBoundChecks.exact_OpenMemberHasBoundedMinimum body α Γ pool seed
  obtain ⟨hit⟩ := hit
  apply casesValue pool seed _ ⟨Derivation.implicationElimination existsMin hit⟩
  intro β j Θ m keep row
  rw [hasRename]
  have pc := renameInto parsed j Θ keep
  simp only [programRename,tripleInputsRename,sucRelabel] at pc
  have out := renameInto computed j Θ keep
  simp only [programRename,tripleInputsRename] at out
  obtain ⟨eqv⟩ := NumberedWindowInternalSparsePackedBoundChecks.exact_OpenPackedPoolMinimum
    C X W s body β Θ (ctx.relabel j) (ty.relabel j) (seed.relabel j) (payload.relabel j) (pool.relabel j) (suc m)
  obtain ⟨pc⟩ := pc
  obtain ⟨out⟩ := out
  obtain ⟨row⟩ := row
  let same := Derivation.implicationElimination eqv (Derivation.conjunctionIntroduction pc out)
  exact enter C X W s _ _ _ m ⟨Derivation.implicationElimination (Derivation.conjunctionRight same)
    (Derivation.conjunctionLeft row)⟩

theorem exact_PackedDomain : ExactPackedDomain := by
  intro C X W s body α Γ ctx ty seed payload vertices
  let A := programGraph contextOption (suc payload) ![ctx,ty,seed] ⊓ unary (scratchVertices C s) vertices seed
  let least := hasLeast C X W s ctx ty seed
  let member := memberGraph vertices seed
  let Δ := A :: Γ
  have d : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have forward : Nonempty (Derivation body (least :: Δ) member) := by
    apply casesLeast C X W s ctx ty seed _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Θ m keep run
    rw [show member = memberGraph vertices seed from rfl,graphRename]
    have h := renameInto ⟨addHyp (Derivation.conjunctionRight d) least⟩ j Θ keep
    rw [unaryRename] at h
    obtain ⟨r⟩ := NumberedWindowInternalSparsePackedSeedPresenceChecks.exact_SeedInGivenVertices
      C X W s body β Θ (ctx.relabel j) (ty.relabel j) (seed.relabel j) m (vertices.relabel j)
    obtain ⟨run⟩ := run
    obtain ⟨h⟩ := h
    exact ⟨Derivation.implicationElimination r (Derivation.conjunctionIntroduction run h)⟩
  have reverse : Nonempty (Derivation body (member :: Δ) least) := by
    apply programCases (membersAtSeed C X W s) ![ctx,ty,seed] _
    intro β j Θ pool keep computed
    rw [show least = hasLeast C X W s ctx ty seed from rfl,hasRename]
    rw [tripleInputsRename] at computed
    have h := renameInto ⟨addHyp (Derivation.conjunctionRight d) member⟩ j Θ keep
    rw [unaryRename] at h
    have pc := renameInto ⟨addHyp (Derivation.conjunctionLeft d) member⟩ j Θ keep
    simp only [programRename,sucRelabel,tripleInputsRename] at pc
    have own : Derivation body (member :: Δ) (memberGraph vertices seed) := Derivation.hypothesis List.mem_cons_self
    have mem := renameInto ⟨own⟩ j Θ keep
    rw [graphRename] at mem
    obtain ⟨rule⟩ := exact_SeedInComputedPool C X W s body β Θ (ctx.relabel j) (ty.relabel j)
      (seed.relabel j) (vertices.relabel j) pool
    obtain ⟨h⟩ := h
    obtain ⟨mem⟩ := mem
    obtain ⟨computed⟩ := computed
    have hit := Derivation.implicationElimination rule
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction h computed) mem)
    exact fromMember C X W s _ _ _ _ pool pc ⟨computed⟩ ⟨hit⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨reverse⟩ := reverse
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction reverse))⟩

#print axioms exact_SeedInComputedPool
#print axioms exact_PackedDomain
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
