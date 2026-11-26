module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoverageOptionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoverageAtTypeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique programRename)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover conjunctionAccept)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchIntro)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue oneConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (poolAtSeed contextOption)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed)
open NumberedWindowInternalMeasuredUnrestrictedWindowIntroProof (exact_OpenUnrestrictedContextOptionMove)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenContextPresentRetape (ctx ty q other r : OTerm α)
    (held : D B Γ (programGraph contextPresent (suc z) ![ctx,ty,q])) :
    D B Γ (programGraph contextPresent (suc z) ![ctx,other,r]) := by
  apply optionGraphCases contextOption ![ctx,ty,q] _
  · intro β j Δ keep zero
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    simp only [tripleInputsRename,zRelabel] at zero
    have read := renameInto held j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at read
    let xs : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,q.relabel j]
    have deny := zeroBranchElim contextOption (constantZero 3) (constantOne 3) (suc z) xs zero read
    obtain ⟨falsehood⟩ := valueUnique (constantZero 3) (suc z) z xs deny (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply falsehood)⟩
  · intro β j Δ payload keep yes
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    simp only [tripleInputsRename] at yes
    let c := ctx.relabel j
    let a := other.relabel j
    let b := r.relabel j
    have moved := exact_OpenUnrestrictedContextOptionMove c (ty.relabel j) (q.relabel j) a b (suc payload) yes
    exact successorBranchIntro contextOption (constantZero 3) (constantOne 3) (suc z) payload
      ![c,a,b] moved (oneConstantValue ![c,a,b])

private theorem ownInputs (C : Program 3) (s : Settings) (ctx ty q cover : OTerm α)
    (seen : D B Γ (unary (scratchVertices C s) cover q)) :
    ∀ i : Fin 2, D B Γ (programGraph ((![poolAtSeed C s,.projection 2] : Fin 2 → Program 3) i)
      (![cover,q] i) ![ctx,ty,q]) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) cover
      ![ctx,ty,q] ![q] seen
    intro j
    obtain rfl := Fin.eq_zero j
    exact projectionValue 2 ![ctx,ty,q]
  · obtain rfl := Fin.eq_zero j
    exact projectionValue 2 ![ctx,ty,q]

theorem exact_OpenOwnSeedTypeRetape (C : Program 3) (s : Settings) (ctx ty other q : OTerm α)
    (held : D B Γ (programGraph (ownSeed C s) (suc z) ![ctx,ty,q])) :
    D B Γ (programGraph (ownSeed C s) (suc z) ![ctx,other,q]) := by
  apply programCases (scratchVertices C s) ![q] _
  intro β j Δ verts keep covered
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
  rw [unaryInputsRename] at covered
  have h := renameInto held j Δ keep
  simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at h
  let c := ctx.relabel j
  let t := ty.relabel j
  let u := other.relabel j
  let a := q.relabel j
  have member : D B Δ (memberGraph verts a) :=
    compositionRecover scratchMember ![poolAtSeed C s,.projection 2] (suc z)
      ![c,t,a] ![verts,a] h (ownInputs C s c t a verts covered)
  exact compositionValue scratchMember ![poolAtSeed C s,.projection 2] (suc z)
    ![c,u,a] ![verts,a] member (ownInputs C s c u a verts covered)

/-- Coverage and own-membership do not read the type slot. This proof
retapes their actual projections, not their closed numeric evaluations. -/
theorem exact_OpenCoverageTypeRetape (C : Program 3) (s : Settings) (ctx ty other q : OTerm α)
    (held : D B Γ (programGraph (conjunction contextPresent (ownSeed C s)) (suc z) ![ctx,ty,q])) :
    D B Γ (programGraph (conjunction contextPresent (ownSeed C s)) (suc z) ![ctx,other,q]) := by
  obtain ⟨both⟩ := conjunctionRecover contextPresent (ownSeed C s) ![ctx,ty,q] held
  exact conjunctionAccept contextPresent (ownSeed C s) ![ctx,other,q]
    (exact_OpenContextPresentRetape ctx ty q other q ⟨Derivation.conjunctionLeft both⟩)
    (exact_OpenOwnSeedTypeRetape C s ctx ty other q ⟨Derivation.conjunctionRight both⟩)

#print axioms exact_OpenContextPresentRetape
#print axioms exact_OpenOwnSeedTypeRetape
#print axioms exact_OpenCoverageTypeRetape
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoverageAtTypeProof
