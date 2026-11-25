module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof

import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue programRename valueUnique)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro zeroBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D)
open NumberedWindowInternalLiteralPackedLeastOnProof
open NumberedWindowInternalLiteralLeastOnMembersProof
open NumberedWindowInternalLiteralLeastOnMinimumProof (exact_OpenLeastOnSeedOrigin)
open NumberedWindowInternalLiteralLeastOnAtPoolsProof (seedOn)
open NumberedWindowInternalLiteralLeastOnEdgeProof (exact_OpenLeastOnSeedReport)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)

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

private theorem positiveCoverage (C : Program 3) (s : Settings)
    (ctx ty seed payload vertices : OTerm α)
    (parsed : D B Γ (programGraph contextOption (suc payload) ![ctx,ty,seed]))
    (pool : D B Γ (unary (scratchVertices C s) vertices seed))
    (member : D B Γ (memberGraph vertices seed)) :
    D B Γ (coverageReport C s ctx seed) := by
  obtain ⟨read⟩ := parsed
  obtain ⟨verts⟩ := pool
  obtain ⟨hit⟩ := member
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
theorem exact_OpenCoverageFromLeastOn (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed chosen : OTerm α)
    (checked : D B Γ (leastOnGraph C E s ctx ty seed chosen)) :
    D B Γ (coverageReport C s ctx seed) := by
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [coverageRename]
    rw [tripleInputsRename] at zero
    have x := renameInto checked j Δ keep
    rw [leastOnRename] at x
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembersOn C E s)
      (suc (chosen.relabel j)) xs zero x
    obtain ⟨bad⟩ := valueUnique (constantZero 3) (suc (chosen.relabel j)) z xs lost
      (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ payload keep parsed
    rw [coverageRename]
    rw [tripleInputsRename] at parsed
    have x := renameInto checked j Δ keep
    rw [leastOnRename] at x
    apply exact_OpenLeastOnSeedReport C E s (ctx.relabel j) (ty.relabel j)
      (seed.relabel j) (chosen.relabel j) _ x
    intro γ k Δ' vertices pool keep' all
    rw [coverageRename]
    have pp := renameInto parsed k Δ' keep'
    rw [programRename,sucRelabel,tripleInputsRename] at pp
    obtain ⟨reports⟩ := all
    let c := (ctx.relabel j).relabel k
    let t := (ty.relabel j).relabel k
    let q := (seed.relabel j).relabel k
    have got := exact_OpenLeastOnSeedOrigin C E s c t q vertices pool ((chosen.relabel j).relabel k)
      ⟨Derivation.conjunctionLeft reports⟩
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight reports)⟩
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight reports)⟩
    exact positiveCoverage C s c t q (payload.relabel k) vertices pp
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight reports)⟩ got

private theorem recoverOwn (C : Program 3) (s : Settings) (ctx ty seed vertices : OTerm α)
    (checked : Nonempty (Derivation B Γ (programGraph (ownSeed C s) (suc z) ![ctx,ty,seed])))
    (cover : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices seed))) :
    Nonempty (Derivation B Γ (memberGraph vertices seed)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,seed]
  apply compositionRecover scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,seed] checked
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![seed] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs

private theorem shiftContextType (ctx ty₁ ty₂ seed tag : OTerm α)
    (held : D B Γ (programGraph contextOption tag ![ctx,ty₁,seed])) :
    D B Γ (programGraph contextOption tag ![ctx,ty₂,seed]) := by
  have read : D B Γ (unary parser tag ctx) := by
    apply compositionRecover parser (fun _ : Fin 1 => .projection 0) tag ![ctx,ty₁,seed] ![ctx] held
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 ![ctx,ty₁,seed]
  apply compositionValue parser (fun _ : Fin 1 => .projection 0) tag ![ctx,ty₂,seed] ![ctx] read
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![ctx,ty₂,seed]

private theorem fromChecks (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty seed vertex : OTerm α)
    (test : D B Γ (programGraph contextPresent (suc z) ![ctx,z,seed]))
    (cover : D B Γ (unary (scratchVertices C s) vertex seed))
    (hit : D B Γ (memberGraph vertex seed)) :
    D B Γ (hasLeastOn C E s ctx ty seed) := by
  apply optionGraphCases contextOption (![ctx,z,seed] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename,zRelabel] at zero
    have yes := renameInto test j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at yes
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,z,seed.relabel j]
    have impossible := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs zero yes
    obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc z) z xs impossible (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename,zRelabel] at parsed
    rw [hasOnRename]
    have left := renameInto cover j Δ keep
    rw [unaryRename] at left
    have mem := renameInto hit j Δ keep
    rw [graphRename] at mem
    let c := ctx.relabel j
    let t := ty.relabel j
    let q := seed.relabel j
    let v := vertex.relabel j
    obtain ⟨atType⟩ := shiftContextType c z t q (suc payload) parsed
    exact exact_OpenLeastOnFromSeed C E s c t q payload v ⟨atType⟩ left mem

theorem exact_OpenLeastOnFromCoverage (C : Program 3) (E : Program 4) (s : Settings)
    (ctx ty raw : OTerm α) (held : D B Γ (coverageReport C s ctx raw)) :
    D B Γ (hasLeastOn C E s ctx ty raw) := by
  obtain ⟨facts⟩ := conjunctionRecover contextPresent (ownSeed C s) ![ctx,z,raw] held
  apply programCases (scratchVertices C s) ![raw] _
  intro β j Δ vertex keep pool
  rw [hasOnRename]
  rw [inputsRename] at pool
  have check := renameInto (⟨Derivation.conjunctionLeft facts⟩ :
    D B Γ (programGraph contextPresent (suc z) ![ctx,z,raw])) j Δ keep
  have own := renameInto (⟨Derivation.conjunctionRight facts⟩ :
    D B Γ (programGraph (ownSeed C s) (suc z) ![ctx,z,raw])) j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at check own
  have belongs := recoverOwn C s (ctx.relabel j) z (raw.relabel j) vertex own pool
  exact fromChecks C E s (ctx.relabel j) (ty.relabel j) (raw.relabel j) vertex check pool belongs

#print axioms exact_OpenCoverageFromLeastOn
#print axioms exact_OpenLeastOnFromCoverage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastOnCoverageProof
