module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoObservationsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoLeastProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof
  (programRename projectionValue compositionValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed packedLeastProgram)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename inputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparsePackedDomainChecks (exact_PackedDomain)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename)
open NumberedWindowInternalLiteralCoveredMemo
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralCoveredMemoObservationsProof (exact_OpenCoveredMemoObservations)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem recoverOwn (C : Program 3) (s : Settings) (ctx ty seed vertices : OTerm α)
    (checked : Nonempty (Derivation body Γ (programGraph (ownSeed C s) (suc z) ![ctx,ty,seed])))
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed))) :
    Nonempty (Derivation body Γ (memberGraph vertices seed)) := by
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
    (held : D body Γ (programGraph contextOption tag ![ctx,ty₁,seed])) :
    D body Γ (programGraph contextOption tag ![ctx,ty₂,seed]) := by
  have read : D body Γ (unary parser tag ctx) := by
    apply compositionRecover parser (fun _ : Fin 1 => .projection 0) tag ![ctx,ty₁,seed] ![ctx] held
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 ![ctx,ty₁,seed]
  apply compositionValue parser (fun _ : Fin 1 => .projection 0) tag ![ctx,ty₂,seed] ![ctx] read
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![ctx,ty₂,seed]

private theorem fromChecks (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed vertex : OTerm α)
    (test : D body Γ (programGraph contextPresent (suc z) ![ctx,z,seed]))
    (cover : D body Γ (unary (scratchVertices C s) vertex seed))
    (hit : D body Γ (memberGraph vertex seed)) :
    D body Γ (hasLeast C X W s ctx ty seed) := by
  apply optionGraphCases contextOption (![ctx,z,seed] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename,zRelabel] at zero
    have yes := renameInto test j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at yes
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,z,seed.relabel j]
    have impossible := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs zero yes
    obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc z) z xs impossible (constantZeroValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename,zRelabel] at parsed
    rw [hasRename]
    have left := renameInto cover j Δ keep
    rw [unaryRename] at left
    have mem := renameInto hit j Δ keep
    rw [graphRename] at mem
    let c := ctx.relabel j
    let t := ty.relabel j
    let q := seed.relabel j
    let v := vertex.relabel j
    obtain ⟨atType⟩ := shiftContextType c z t q (suc payload) parsed
    obtain ⟨domain⟩ := exact_PackedDomain C X W s body β Δ c t q payload v
    obtain ⟨prog⟩ := left
    obtain ⟨belongs⟩ := mem
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight
      (Derivation.implicationElimination domain (Derivation.conjunctionIntroduction atType prog))) belongs⟩

theorem exact_OpenLeastFromCoverage (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty raw : OTerm α) (held : D body Γ (coverageReport C s ctx raw)) :
    D body Γ (hasLeast C X W s ctx ty raw) := by
  obtain ⟨facts⟩ := conjunctionRecover contextPresent (ownSeed C s) ![ctx,z,raw] held
  apply programCases (scratchVertices C s) ![raw] _
  intro β j Δ vertex keep pool
  rw [hasRename]
  rw [inputsRename] at pool
  have check := renameInto (⟨Derivation.conjunctionLeft facts⟩ :
    D body Γ (programGraph contextPresent (suc z) ![ctx,z,raw])) j Δ keep
  have own := renameInto (⟨Derivation.conjunctionRight facts⟩ :
    D body Γ (programGraph (ownSeed C s) (suc z) ![ctx,z,raw])) j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at check own
  have belongs := recoverOwn C s (ctx.relabel j) z (raw.relabel j) vertex own pool
  exact fromChecks C X W s (ctx.relabel j) (ty.relabel j) (raw.relabel j) vertex check pool belongs

/-- A successful original covered-memo window already supplies the
domain of its physically paired least program. With no numeral
assumption this retains the exact scope and raw input in the query. -/
theorem exact_OpenCoveredMemoLeast (C : Program 3) (X : Program 2) (s : Settings)
    (base : Program 2) (T V : Program 1) (ctx ty raw : OTerm α)
    (held : D body Γ (windowGraph (coveredMemoWindow C s base T V) ctx ty raw)) :
    D body Γ (hasLeast C X (coveredMemoWindow C s base T V) s ctx ty raw ⊓ unary V (suc z) raw) := by
  obtain ⟨obs⟩ := exact_OpenCoveredMemoObservations C s base T V ctx ty raw held
  obtain ⟨query⟩ := exact_OpenLeastFromCoverage C X (coveredMemoWindow C s base T V) s ctx ty raw
    ⟨Derivation.conjunctionLeft obs⟩
  exact ⟨Derivation.conjunctionIntroduction query (Derivation.conjunctionRight obs)⟩

#print axioms exact_OpenLeastFromCoverage
#print axioms exact_OpenCoveredMemoLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoLeastProof
