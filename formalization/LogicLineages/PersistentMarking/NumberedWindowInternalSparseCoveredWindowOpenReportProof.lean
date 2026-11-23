module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverOccurrenceSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalControlGraphSupportProof (programRename projectionValue compositionValue valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)
open NumberedWindowInternalSparseCoverOccurrenceSyntaxProof (coverIntro coverRename)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
def ownSeed (C : Program 3) (s : Settings) : Program 3 :=
  .composition scratchMember ![poolAtSeed C s,.projection 2]

def contextPresent : Program 3 := branch contextOption (constantZero 3) (constantOne 3)

def coveredWindow (C : Program 3) (s : Settings) (baseW : Program 3) : Program 3 :=
  conjunction baseW (conjunction contextPresent (ownSeed C s))

def ExactCoveredWindowReport : Prop :=
  ∀ (C : Program 3) (X : Program 2) (s : Settings) (baseW : Program 3)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed : OTerm α),
    let W := coveredWindow C s baseW
    Nonempty (Derivation body Γ ((windowAt W ctx ty seed).imp
      (windowAt baseW ctx ty seed ⊓ (occursInCover C s seed seed ⊓ hasLeast C X W s ctx ty seed))))

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (s : Settings) (baseW : Program 3)

private theorem recoverOwn (ctx ty seed vertices : OTerm α)
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

private theorem fromChecks (ctx ty seed vertices : OTerm α)
    (context : Nonempty (Derivation body Γ (programGraph contextPresent (suc z) ![ctx,ty,seed])))
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)))
    (hit : Nonempty (Derivation body Γ (memberGraph vertices seed))) :
    Nonempty (Derivation body Γ (hasLeast C X (coveredWindow C s baseW) s ctx ty seed)) := by
  apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α) _
  · intro β j Δ keep zero
    rw [tripleInputsRename] at zero
    have yes := renameInto context j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at yes
    let xs := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have impossible := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs zero yes
    obtain ⟨eq⟩ := valueUnique (constantZero 3) (suc z) z xs impossible (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply eq)⟩
  · intro β j Δ payload keep parsed
    rw [tripleInputsRename] at parsed
    rw [hasRename]
    have v := renameInto cover j Δ keep
    rw [unaryRename] at v
    have h := renameInto hit j Δ keep
    rw [graphRename] at h
    obtain ⟨rule⟩ := NumberedWindowInternalSparsePackedDomainChecks.exact_PackedDomain C X (coveredWindow C s baseW)
      s body β Δ (ctx.relabel j) (ty.relabel j) (seed.relabel j) payload (vertices.relabel j)
    obtain ⟨parsed⟩ := parsed
    obtain ⟨v⟩ := v
    obtain ⟨h⟩ := h
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight
      (Derivation.implicationElimination rule (Derivation.conjunctionIntroduction parsed v))) h⟩

theorem exact_CoveredWindowReport : ExactCoveredWindowReport := by
  intro C X s baseW body α Γ ctx ty seed
  let W := coveredWindow C s baseW
  let xs := ![ctx,ty,seed]
  let G := programGraph W (suc z) xs
  let Δ := G :: Γ
  have h : Derivation body Δ G := Derivation.hypothesis List.mem_cons_self
  obtain ⟨outer⟩ := conjunctionRecover baseW (conjunction contextPresent (ownSeed C s)) xs ⟨h⟩
  obtain ⟨guards⟩ := conjunctionRecover contextPresent (ownSeed C s) xs ⟨Derivation.conjunctionRight outer⟩
  have extra : Nonempty (Derivation body Δ (occursInCover C s seed seed ⊓ hasLeast C X W s ctx ty seed)) := by
    apply programCases (scratchVertices C s) ![seed] _
    intro β j Θ vertex keep output
    rw [conjunctionRename,coverRename,hasRename]
    rw [unaryInputsRename] at output
    have pc := renameInto ⟨Derivation.conjunctionLeft guards⟩ j Θ keep
    have own := renameInto ⟨Derivation.conjunctionRight guards⟩ j Θ keep
    simp only [programRename,xs,tripleInputsRename,sucRelabel,zRelabel] at pc own
    have hit := recoverOwn C s _ _ _ vertex own output
    obtain ⟨member⟩ := coverIntro C s _ _ vertex output hit
    obtain ⟨existsValue⟩ := fromChecks C X s baseW _ _ _ vertex pc output hit
    exact ⟨Derivation.conjunctionIntroduction member existsValue⟩
  obtain ⟨extra⟩ := extra
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft outer) extra)⟩

#print axioms exact_CoveredWindowReport
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowOpenReportProof
