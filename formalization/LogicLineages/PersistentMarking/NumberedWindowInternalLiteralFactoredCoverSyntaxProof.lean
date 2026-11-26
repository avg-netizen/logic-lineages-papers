module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEnrichedEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPositiveBooleanProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFactoredCoverSyntaxProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue valueUnique programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim)
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
open NumberedWindowInternalSparseCoverScratch (coverOption)
open NumberedWindowInternalSparseCoverScratchOpenTargets (callbackTape)
open NumberedWindowInternalSparseCoverScratchOpenSyntaxProof (callbackFromOption)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalFactoredCoverTargets (factoredCover rawCall generatorCall)
open NumberedWindowInternalLiteralPositiveBooleanProof (exact_OpenPositiveNormalization)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A real successful factored cover must have taken its actual raw syntax
arm. The encoder chooses a unit-test program so the recovered graph
has exact value ONE, even on arbitrary symbolic inputs. -/
theorem exact_OpenFactoredCoverSyntax (V M : Program 1) (G : Program 3) (s : Settings)
    (q covered : OTerm α)
    (positive : D B Γ (unary (coverOption (factoredCover (normalize V) M G) s) (suc covered) q)) :
    D B Γ (unary (normalize V) (suc z) q) := by
  apply optionGraphCases (normalize V) ![q] _
  · intro β j Δ keep zero
    rw [unaryRename,sucRelabel,zRelabel]
    simp only [unaryInputsRename,zRelabel] at zero
    have hold := renameInto positive j Δ keep
    rw [unaryRename,sucRelabel] at hold
    let a := q.relabel j
    let v := covered.relabel j
    let xs := callbackTape s a
    have rawZero : D B Δ (programGraph (rawCall (normalize V)) z xs) := by
      apply compositionValue (normalize V) (fun _ : Fin 1 => .projection 2) z xs ![a] zero
      intro i
      obtain rfl := Fin.eq_zero i
      exact projectionValue 2 xs
    have actual := callbackFromOption (factoredCover (normalize V) M G) s (suc v) a hold
    have reject := zeroBranchElim (rawCall (normalize V)) (constantZero 3) (generatorCall M G)
      (suc v) xs rawZero actual
    obtain ⟨impossible⟩ := valueUnique (constantZero 3) (suc v) z xs reject (zeroConstantValue xs)
    exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩
  · intro β j Δ event keep active
    rw [unaryRename,sucRelabel,zRelabel]
    rw [unaryInputsRename] at active
    exact exact_OpenPositiveNormalization V ![q.relabel j] event active

#print axioms exact_OpenFactoredCoverSyntax
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFactoredCoverSyntaxProof
