module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFactoredCoverSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenBranchProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoverageOptionProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique programRename)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization (normalize)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparseCoverScratchOpenBranchProof (scratchZero)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed)
open NumberedWindowInternalSparseScratchMembership (scratchMember memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalLiteralFactoredCoverSyntaxProof (exact_OpenFactoredCoverSyntax)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_CoverageReportRename (C : Program 3) (s : Settings) {β : Type}
    (ctx q : OTerm α) (j : α → β) :
    (coverageReport C s ctx q).relabel j = coverageReport C s (ctx.relabel j) (q.relabel j) := by
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel]

theorem exact_OpenCoverageOwnAtScratch (C : Program 3) (s : Settings) (ctx q vertices : OTerm α)
    (checked : D B Γ (coverageReport C s ctx q))
    (cover : D B Γ (unary (scratchVertices C s) vertices q)) :
    D B Γ (memberGraph vertices q) := by
  let xs : Fin 3 → OTerm α := ![ctx,z,q]
  obtain ⟨parts⟩ := conjunctionRecover contextPresent (ownSeed C s) xs checked
  apply compositionRecover scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,q]
    ⟨Derivation.conjunctionRight parts⟩
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![q] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs

private theorem nilCannotContain (q : OTerm α)
    (held : D B Γ (memberGraph z q)) : D B Γ (⊥ : Formula α) := by
  have none := nilRecover memberBase memberStep (suc z) ![q] held
  obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![q] none (zeroConstantValue ![q])
  exact ⟨sucNeZeroApply bad⟩

/-- The original physical own-membership report excludes a missing cover.
The original positive cover option is selected in the same calculus. -/
theorem exact_OpenCoverageOptionCases (C : Program 3) (s : Settings) (ctx q : OTerm α)
    (goal : Formula α) (own : D B Γ (coverageReport C s ctx q))
    (use : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (verts : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      D B Δ (unary (coverOption C s) (suc verts) (q.relabel j)) →
      D B Δ (goal.relabel j)) : D B Γ goal := by
  apply optionGraphCases (coverOption C s) ![q] _ 
  · intro β j Δ keep absent
    simp only [unaryInputsRename,zRelabel] at absent
    have kept := renameInto own j Δ keep
    rw [exact_CoverageReportRename] at kept
    have no := scratchZero C s (q.relabel j) absent
    obtain ⟨falsehood⟩ := nilCannotContain (q.relabel j)
      (exact_OpenCoverageOwnAtScratch C s (ctx.relabel j) (q.relabel j) z kept no)
    exact ⟨Derivation.explosion falsehood⟩
  · intro β j Δ verts keep present
    rw [unaryInputsRename] at present
    exact use β j Δ verts keep present

theorem exact_OpenFactoredSyntaxFromCoverage (V M : Program 1) (G : Program 3) (s : Settings)
    (ctx q : OTerm α) (own : D B Γ (coverageReport (factoredCover (normalize V) M G) s ctx q)) :
    D B Γ (unary (normalize V) (suc z) q) := by
  apply exact_OpenCoverageOptionCases (factoredCover (normalize V) M G) s ctx q _ own
  intro β j Δ verts keep present
  rw [unaryRename,sucRelabel,zRelabel]
  exact exact_OpenFactoredCoverSyntax V M G s (q.relabel j) verts present

#print axioms exact_CoverageReportRename
#print axioms exact_OpenCoverageOwnAtScratch
#print axioms exact_OpenCoverageOptionCases
#print axioms exact_OpenFactoredSyntaxFromCoverage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoverageOptionProof
