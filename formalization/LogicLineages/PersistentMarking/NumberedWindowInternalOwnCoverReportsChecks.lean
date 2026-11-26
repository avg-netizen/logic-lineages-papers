module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredWindowNumericProof
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

import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction constantZero)
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
open NumberedWindowInternalSparseCoveredWindowTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
open NumberedWindowInternalOwnCoverReportsTargets
open NumberedWindowInternalFactoredCoverTargets (factoredCover rawCall generatorCall)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape)
open NumberedWindowInternalSparseCoverScratchOpenChecks (exact_ScratchCallbackZero)
open NumberedWindowInternalSparseCoverOccurrenceTargets (coverRow)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open ID1Completion.InternalLessThanSupportProof (oneConstantValue)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchIntro successorBranchIntro)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open SourceComputabilityFormulaSupportProof (existsOne)
open List.Vector

theorem exact_SyntaxFlagCalibration : ExactSyntaxFlagCalibration := by
  intro V hV q
  rw [syntaxFlag,evalBranch]
  change (if evaluate V (q ::ᵥ nil) = 0 then 0 else 1) = (syntaxBits q).1.toNat
  rw [hV q]
  cases (syntaxBits q).1 <;> rfl

private theorem syntaxFrom (baseV M : Program 1) (G : Program 3) (s : Settings)
    (seed vertices : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices (factoredCover (syntaxFlag baseV) M G) s) vertices seed)))
    (member : Nonempty (Derivation body Γ (memberGraph vertices seed))) :
    Nonempty (Derivation body Γ (unary (syntaxFlag baseV) (suc z) seed)) := by
  let V := syntaxFlag baseV
  let C := factoredCover V M G
  apply optionGraphCases baseV (![seed] : Fin 1 → OTerm α) _
  · intro β j Δ keep zero
    rw [unaryInputsRename] at zero
    let v := seed.relabel j
    let xs := callbackTape s v
    have flag := zeroBranchIntro baseV (constantZero 1) (constantOne 1) z ![v] zero (zeroConstantValue _)
    have raw : Nonempty (Derivation body Δ (programGraph (rawCall V) z xs)) := by
      apply compositionValue V (fun _ : Fin 1 => .projection (2 : Fin 3)) z xs ![v] flag
      intro i
      obtain rfl := Fin.eq_zero i
      exact projectionValue 2 xs
    have missing := zeroBranchIntro (rawCall V) (constantZero 3) (generatorCall M G) z xs raw (zeroConstantValue xs)
    obtain ⟨noCover⟩ := exact_ScratchCallbackZero C s body β Δ v
    obtain ⟨missing⟩ := missing
    have empty := Derivation.implicationElimination noCover missing
    have actual := renameInto cover j Δ keep
    rw [unaryRename] at actual
    have same := valueUnique (scratchVertices C s) (vertices.relabel j) z ![v] actual ⟨empty⟩
    have hit := renameInto member j Δ keep
    rw [graphRename] at hit
    have impossible := headTransport scratchMember (suc z) (vertices.relabel j) z ![v] same hit
    have base := nilRecover memberBase memberStep (suc z) (![v] : Fin 1 → OTerm β) impossible
    obtain ⟨bad⟩ := valueUnique memberBase (suc z) z ![v] base (zeroConstantValue _)
    exact ⟨Derivation.explosion (sucNeZeroApply bad)⟩
  · intro β j Δ k keep accepted
    rw [unaryInputsRename] at accepted
    simp only [unaryRename,sucRelabel,zRelabel]
    exact successorBranchIntro baseV (constantZero 1) (constantOne 1) (suc z) k ![seed.relabel j]
      accepted (oneConstantValue _)

private theorem ownFrom (C : Program 3) (s : Settings) (ctx ty seed vertices : OTerm α)
    (cover : Nonempty (Derivation body Γ (unary (scratchVertices C s) vertices seed)))
    (hit : Nonempty (Derivation body Γ (memberGraph vertices seed))) :
    Nonempty (Derivation body Γ (programGraph (ownSeed C s) (suc z) ![ctx,ty,seed])) := by
  let xs := ![ctx,ty,seed]
  apply compositionValue scratchMember ![poolAtSeed C s,.projection 2] (suc z) xs ![vertices,seed] hit
  intro i
  refine Fin.cases ?_ (fun k => ?_) i
  · apply compositionValue (scratchVertices C s) (fun _ : Fin 1 => .projection 2) vertices xs ![seed] cover
    intro k
    obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs
  · obtain rfl := Fin.eq_zero k
    exact projectionValue 2 xs

theorem exact_OwnCoverReports : ExactOwnCoverReports := by
  intro baseV M G s body α Γ ctx ty seed V C
  let O := occursInCover C s seed seed
  let j : α → α ⊕ Fin 1 := Sum.inl
  let v := seed.relabel j
  let vertices : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let row := coverRow C s v v vertices
  let Δ := row :: (O :: Γ).map weaken
  have supplied : Derivation body (O :: Γ) (existsOne row) := Derivation.hypothesis List.mem_cons_self
  have observed : Derivation body Δ row := Derivation.hypothesis List.mem_cons_self
  have h := Derivation.conjunctionLeft observed
  have k := Derivation.conjunctionRight observed
  obtain ⟨flag⟩ := syntaxFrom baseV M G s v vertices ⟨h⟩ ⟨k⟩
  obtain ⟨own⟩ := ownFrom C s (ctx.relabel j) (ty.relabel j) v vertices ⟨h⟩ ⟨k⟩
  let A := unary V (suc z) seed ⊓ programGraph (ownSeed C s) (suc z) ![ctx,ty,seed]
  have final : Derivation body Δ (weaken A) := by
    change Derivation body Δ (A.relabel j)
    simp only [A,conjunctionRename,unaryRename,programRename,tripleInputsRename,sucRelabel,zRelabel]
    exact Derivation.conjunctionIntroduction flag own
  exact ⟨Derivation.implicationIntroduction (Derivation.existentialElimination supplied final)⟩

#print axioms exact_SyntaxFlagCalibration
#print axioms exact_OwnCoverReports
end LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsChecks
