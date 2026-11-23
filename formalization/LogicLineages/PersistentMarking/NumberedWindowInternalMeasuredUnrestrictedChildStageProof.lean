module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredAuxOwnCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureCombineOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredStageScratchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GuardedSourceSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedChildStageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalCoverGrammarStageTargets (grammarTerms termsGraph)
open NumberedWindowInternalFactoredAuxOwnCoverTargets (headsTerm typesTerm installedCover)
open NumberedWindowInternalChosenAuxMeasureCombineOpenTargets (codePair)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow contextPresent ownSeed)
open NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof (exact_OpenUnrestrictedWindowReports)
open NumberedWindowInternalFactoredStageScratchProof (exact_OpenFactoredStageScratch)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The installed stage's report follows from the real physical grammar
program, not a numeric selection or a change of generator. -/
theorem exact_OpenUnrestrictedStageTermsCases (P : Program 5) (A : Program 2) (s : Settings)
    (depth width : OTerm α) (goal : Formula α)
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (terms : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (termsGraph P A terms (depth.relabel j)
        (headsTerm s β) (typesTerm s β) (width.relabel j))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases (grammarTerms P A) ![depth,headsTerm s α,typesTerm s α,width] goal
  intro β j Δ result keep row
  have actual : Nonempty (Derivation B Δ (termsGraph P A result (depth.relabel j)
      (headsTerm s β) (typesTerm s β) (width.relabel j))) := by
    simpa only [quadInputsRename,headsTerm,typesTerm,numeralRename] using row
  exact next β j Δ result keep actual

private theorem ownFromWindow (C : Program 3) (s : Settings) (baseW : Program 3)
    (V : Program 1) (ctx ty child vertices : OTerm α)
    (held : Nonempty (Derivation B Γ (windowAt (window C s baseW V) ctx ty child)))
    (scratch : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices child))) :
    Nonempty (Derivation B Γ (memberGraph vertices child)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,child]
  obtain ⟨outer⟩ := conjunctionRecover (syntaxWindow baseW V)
    (conjunction contextPresent (ownSeed C s)) xs held
  obtain ⟨bits⟩ := conjunctionRecover contextPresent (ownSeed C s) xs ⟨Derivation.conjunctionRight outer⟩
  apply compositionRecover scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,child]
    ⟨Derivation.conjunctionRight bits⟩
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![child] scratch
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs

/-- At the actual measured child coordinates, its held own-checked window
puts the same child in the stage's actual ordered original term list. -/
theorem exact_OpenUnrestrictedMeasuredChildStage (V M : Program 1) (P : Program 5) (A : Program 2)
    (s : Settings) (baseW : Program 3) (ctx ty child m depth width vertices : OTerm α) :
    let C := installedCover V M P A
    Nonempty (Derivation B Γ (windowAt (window C s baseW V) ctx ty child)) →
    Nonempty (Derivation B Γ (unary M m child)) →
    Nonempty (Derivation B Γ (codePair m depth width)) →
    Nonempty (Derivation B Γ (termsGraph P A vertices depth (headsTerm s α) (typesTerm s α) width)) →
    Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices child ⊓ memberGraph vertices child)) := by
  intro C held measured coords stage
  obtain ⟨reports⟩ := exact_OpenUnrestrictedWindowReports C s baseW V ctx ty child held
  obtain ⟨scratch⟩ := (exact_OpenFactoredStageScratch V M P A s m depth width vertices child
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight reports)⟩ measured coords stage).2
  obtain ⟨member⟩ := ownFromWindow C s baseW V ctx ty child vertices held ⟨scratch⟩
  exact ⟨Derivation.conjunctionIntroduction scratch member⟩

#print axioms exact_OpenUnrestrictedStageTermsCases
#print axioms exact_OpenUnrestrictedMeasuredChildStage
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedChildStageProof
