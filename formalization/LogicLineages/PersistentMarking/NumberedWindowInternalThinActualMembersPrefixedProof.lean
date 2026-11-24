module

public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinFuelBudgetChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersPrefixedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseDirectedFilter (pass passTape passGraph)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength exact_OpenRoundSuccessor)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalScratchInclusionThinProof (included)
open NumberedWindowInternalThinPrefixedRoundsTargets (prefixed)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinFuelBudgetChecks (exact_LengthStability)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atActualLength (bound : CountLengthBound) (pred : ExactRetainedPredecessor)
    (strict : InternalStrictDecrease) (E : Program 4) (vertices ctx ty seed pool later n : OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (members E) pool (membersTape vertices ctx ty seed))))
    (length : Nonempty (Derivation B Γ (unary poolLength n vertices)))
    (passed : Nonempty (Derivation B Γ (passGraph E later vertices pool ctx ty))) :
    Nonempty (Derivation B Γ (prefixed E vertices ctx ty pool later)) := by
  obtain ⟨memberView⟩ := exact_OpenMembersAtLength E B α Γ pool n vertices ctx ty seed
  obtain ⟨nextView⟩ := exact_OpenRoundSuccessor E B α Γ later n vertices ctx ty seed pool
  obtain ⟨stable⟩ := exact_LengthStability bound pred strict E B α Γ vertices ctx ty seed n pool later
  obtain ⟨m⟩ := held
  obtain ⟨l⟩ := length
  obtain ⟨p⟩ := passed
  have before := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination memberView l)) m
  have after := Derivation.implicationElimination
    (Derivation.conjunctionRight (Derivation.implicationElimination nextView before)) p
  have inc := Derivation.implicationElimination stable
    (Derivation.conjunctionIntroduction l (Derivation.conjunctionIntroduction before after))
  exact ⟨Derivation.conjunctionIntroduction p inc⟩

/-- The actual physical members output is pre-fixed at every genuinely
observed pass on itself, without caller-supplied length or further round. -/
theorem exact_OpenThinMembersPrefixed (bound : CountLengthBound) (pred : ExactRetainedPredecessor)
    (strict : InternalStrictDecrease) (E : Program 4) (vertices ctx ty seed pool later : OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (members E) pool (membersTape vertices ctx ty seed))))
    (passed : Nonempty (Derivation B Γ (passGraph E later vertices pool ctx ty))) :
    Nonempty (Derivation B Γ (prefixed E vertices ctx ty pool later)) := by
  apply programCases poolLength (![vertices] : Fin 1 → OTerm α) _
  intro β j Δ n keep length
  rw [unaryInputsRename] at length
  have m := renameInto held j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at m
  have p := renameInto passed j Δ keep
  rw [passRename] at p
  change Nonempty (Derivation B Δ ((prefixed E vertices ctx ty pool later).relabel j))
  have normalized :
      (prefixed E vertices ctx ty pool later).relabel j =
        prefixed E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (pool.relabel j) (later.relabel j) := by
    simp only [prefixed,ID1Completion.InternalRecursionGraphStepSyntaxProof.conjunctionRename,
      passRename,NumberedWindowInternalScratchInclusionThinProof.includedRename]
  rw [normalized]
  exact atActualLength bound pred strict E (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
    (seed.relabel j) (pool.relabel j) (later.relabel j) n m length p

/-- Choose the actual successor pass now. Downstream may consume this
pre-fixed report using the original thin arbitrary pre-fixed rounds API. -/
theorem exact_OpenThinMembersPrefixedCases (bound : CountLengthBound) (pred : ExactRetainedPredecessor)
    (strict : InternalStrictDecrease) (E : Program 4) (vertices ctx ty seed pool : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (programGraph (members E) pool (membersTape vertices ctx ty seed))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (later : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ
        (prefixed E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (pool.relabel j) later)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases (pass E) (passTape vertices pool ctx ty) goal
  intro β j Δ later keep p
  simp only [passTape,quadInputsRename] at p
  have m := renameInto held j Δ keep
  simp only [programRename,membersTape,quadInputsRename] at m
  exact next β j Δ later keep
    (exact_OpenThinMembersPrefixed bound pred strict E (vertices.relabel j) (ctx.relabel j) (ty.relabel j)
      (seed.relabel j) (pool.relabel j) later m p)

#print axioms exact_OpenThinMembersPrefixed
#print axioms exact_OpenThinMembersPrefixedCases
end LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersPrefixedProof
