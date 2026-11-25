module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastCoverageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed minimumAtMembers)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainChecks (exact_PackedDomain)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (enter)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem coverageRename (C : Program 3) (s : Settings) {β : Type}
    (ctx seed : OTerm α) (j : α → β) :
    (coverageReport C s ctx seed).relabel j = coverageReport C s (ctx.relabel j) (seed.relabel j) := by
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel]

private theorem contextIgnoreType (ctx ty seed payload : OTerm α)
    (parsed : D B Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])) :
    D B Γ (programGraph contextOption (suc payload) ![ctx,z,seed]) := by
  have read : D B Γ (unary parser (suc payload) ctx) := by
    apply compositionRecover parser (fun _ : Fin 1 => .projection 0) (suc payload)
      ![ctx,ty,seed] ![ctx] parsed
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 ![ctx,ty,seed]
  apply compositionValue parser (fun _ : Fin 1 => .projection 0) (suc payload) ![ctx,z,seed] ![ctx] read
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![ctx,z,seed]

private theorem positiveCoverage (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed chosen payload vertices : OTerm α)
    (checked : D B Γ (leastGraph C X W s ctx ty seed chosen))
    (parsed : D B Γ (programGraph contextOption (suc payload) ![ctx,ty,seed]))
    (pool : D B Γ (unary (scratchVertices C s) vertices seed)) :
    D B Γ (coverageReport C s ctx seed) := by
  obtain ⟨dom⟩ := exact_PackedDomain C X W s B α Γ ctx ty seed payload vertices
  obtain ⟨has⟩ := enter C X W s ctx ty seed chosen checked
  obtain ⟨read⟩ := parsed
  obtain ⟨verts⟩ := pool
  have hit := Derivation.implicationElimination
    (Derivation.conjunctionLeft (Derivation.implicationElimination dom
      (Derivation.conjunctionIntroduction read verts))) has
  let xs : Fin 3 → OTerm α := ![ctx,z,seed]
  have own : D B Γ (programGraph (ownSeed C s) (suc z) xs) := by
    apply compositionValue scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,seed] ⟨hit⟩
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![seed] ⟨verts⟩
      intro k
      obtain rfl := Fin.eq_zero k
      exact projectionValue 2 xs
    · obtain rfl := Fin.eq_zero k
      exact projectionValue 2 xs
  have context : D B Γ (programGraph contextPresent (suc z) xs) := by
    apply successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) payload xs
    · exact contextIgnoreType ctx ty seed payload ⟨read⟩
    · exact oneConstantValue xs
  exact conjunctionAccept contextPresent (ownSeed C s) xs context own

/-- A successful physical least query exposes the accepted context and
membership of its own seed in the computed cover, not just membership
of the selected minimum in the computed reachable list. -/
theorem exact_OpenCoverageFromLeast (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed chosen : OTerm α)
    (checked : D B Γ (leastGraph C X W s ctx ty seed chosen)) :
    D B Γ (coverageReport C s ctx seed) := by
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [coverageRename]
    rw [tripleInputsRename] at zero
    have x := renameInto checked j Δ keep
    rw [leastRename] at x
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
      (suc (chosen.relabel j)) xs zero x
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc (chosen.relabel j)) z xs lost
      (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep parsed
    rw [coverageRename]
    rw [tripleInputsRename] at parsed
    have x := renameInto checked j Δ keep
    rw [leastRename] at x
    apply programCases (scratchVertices C s) ![seed.relabel j] _
    intro γ k Δ' vertices keep' pool
    rw [coverageRename]
    rw [inputsRename] at pool
    have y := renameInto x k Δ' keep'
    rw [leastRename] at y
    have pp := renameInto parsed k Δ' keep'
    rw [programRename,sucRelabel,tripleInputsRename] at pp
    exact positiveCoverage C X W s _ _ _ _ _ vertices y pp pool

#print axioms exact_OpenCoverageFromLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastCoverageProof
