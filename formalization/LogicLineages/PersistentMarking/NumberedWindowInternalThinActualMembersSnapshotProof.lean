module

public import LogicLineages.PersistentMarking.NumberedWindowInternalThinMembersClosureTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalThinPrefixedRoundsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersPrefixedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOpenRoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersSnapshotProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparseDirectedRounds (members membersTape poolLength)
open NumberedWindowInternalSparseOpenRoundsTargets (roundGraph)
open NumberedWindowInternalSparseOpenRoundsChecks (exact_OpenMembersAtLength)
open NumberedWindowInternalSparsePassWindowSyntaxProof (passRename)
open NumberedWindowInternalSparseRoundWindowMotiveProof (roundRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseRetainedScanTargets (ExactRetainedPredecessor)
open NumberedWindowInternalScratchInclusionThinProof (includedRename)
open NumberedWindowInternalThinPrefixedRoundsTargets (prefixed)
open NumberedWindowInternalThinRoundExhaustionTargets (CountLengthBound)
open NumberedWindowInternalThinUncoveredCountTargets (InternalStrictDecrease)
open NumberedWindowInternalThinActualMembersPrefixedProof (exact_OpenThinMembersPrefixedCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The complete physical terminal snapshot of the already chosen pool. -/
def snapshot (E : Program 4) (vertices ctx ty seed pool size later : OTerm α) : Formula α :=
  unary poolLength size vertices ⊓
    (roundGraph E pool size vertices ctx ty seed ⊓ prefixed E vertices ctx ty pool later)

theorem snapshotRename {β : Type} (E : Program 4) (vertices ctx ty seed pool size later : OTerm α)
    (j : α → β) :
    (snapshot E vertices ctx ty seed pool size later).relabel j =
      snapshot E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
        (pool.relabel j) (size.relabel j) (later.relabel j) := by
  simp only [snapshot, prefixed, conjunctionRename, unaryRename, roundRename, passRename, includedRename]

/-- Open the literal length and the literal next pass, keeping the actual
length-round report at the very same ordered members output. -/
theorem exact_OpenThinActualMembersSnapshot (bound : CountLengthBound) (pred : ExactRetainedPredecessor)
    (strict : InternalStrictDecrease) (E : Program 4) (vertices ctx ty seed pool : OTerm α) (goal : Formula α)
    (held : Nonempty (Derivation B Γ (programGraph (members E) pool (membersTape vertices ctx ty seed))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (size later : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ
        (snapshot E (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j)
          (pool.relabel j) size later)) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases poolLength (![vertices] : Fin 1 → OTerm α) goal
  intro β j Δ size keep len
  rw [unaryInputsRename] at len
  have m := renameInto held j Δ keep
  simp only [programRename, membersTape, quadInputsRename] at m
  have round : Nonempty (Derivation B Δ
      (roundGraph E (pool.relabel j) size (vertices.relabel j) (ctx.relabel j)
        (ty.relabel j) (seed.relabel j))) := by
    obtain ⟨view⟩ := exact_OpenMembersAtLength E B β Δ (pool.relabel j) size (vertices.relabel j)
      (ctx.relabel j) (ty.relabel j) (seed.relabel j)
    obtain ⟨l⟩ := len
    obtain ⟨h⟩ := m
    exact ⟨Derivation.implicationElimination
      (Derivation.conjunctionLeft (Derivation.implicationElimination view l)) h⟩
  apply exact_OpenThinMembersPrefixedCases bound pred strict E
    (vertices.relabel j) (ctx.relabel j) (ty.relabel j) (seed.relabel j) (pool.relabel j) (goal.relabel j) m
  intro γ k Ω later retain fixed
  have both (f : Formula α) (hf : f ∈ Γ) : f.relabel (k ∘ j) ∈ Ω := by
    rw [← formulaRelabelComposition j k f]
    exact retain _ (keep f hf)
  have len' := renameInto (phi := unary poolLength size (vertices.relabel j)) len k Ω retain
  have round' := renameInto round k Ω retain
  simp only [unaryRename, Term.relabel_relabel] at len'
  simp only [roundRename, Term.relabel_relabel] at round'
  simp only [Term.relabel_relabel] at fixed
  obtain ⟨l⟩ := len'
  obtain ⟨r⟩ := round'
  obtain ⟨f⟩ := fixed
  rw [formulaRelabelComposition j k goal]
  exact next γ (k ∘ j) Ω (size.relabel k) later both
    ⟨Derivation.conjunctionIntroduction l (Derivation.conjunctionIntroduction r f)⟩

#print axioms snapshotRename
#print axioms exact_OpenThinActualMembersSnapshot
end LogicLineages.PersistentMarking.NumberedWindowInternalThinActualMembersSnapshotProof
