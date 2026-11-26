module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafValuesProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRootDispatchNumericProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFitProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (conjunction)
open InternalAcceptanceCalibrationProof (evalBranch)
open InternalApplicationStepPeelEvaluationSupportProof (conjunctionEvaluation)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowRootDispatchAlgorithm (fixed parts)
open NumberedWindowFieldAlgorithm (unpackNode packNode)
open NumberedWindowInternalLiteralAuxRootLeaf
open NumberedWindowInternalLiteralAuxRootNumericProof
open NumberedWindowInternalLiteralAuxRootLeafValuesProof (auxValue functionHeaderOf targetValue)
open NumberedWindowInternalSparseRawFunctionFrameNumericASTProof (tape)
open NumberedWindowInternalLiteralRootDispatchNumericProof (LeafFit)

private theorem addCheck (p g : Program 3) (v : List.Vector Nat 3) (b : Bool)
    (old : evaluate p v = b.toNat) (ok : b = true → evaluate g v = 1) :
    evaluate (conjunction p g) v = b.toNat := by
  rw [conjunctionEvaluation,old]
  cases b with
  | false => rfl
  | true => simp [ok rfl]

private theorem betaObservation (entries : Entries) (heads : List Nat)
    (q r d c f a : Nat) (fs : List Nat)
    (hq : unpackNode q = some (6,[d,c,f,a]))
    (truePart : parts (fixed entries heads) q r 6 fs = true) :
    ∃ row, unpackNode f = some (2,row) := by
  cases fs with
  | cons _ _ => cases truePart
  | nil =>
    by_contra miss
    change NumberedWindowBinderRootAlgorithm.beta q r = true at truePart
    rw [exact_AuxiliaryBetaRequiresLambda q r d c f a hq miss] at truePart
    cases truePart

private theorem bottomObservation (entries : Entries) (heads : List Nat)
    (q r d c f a : Nat) (fs : List Nat)
    (hq : unpackNode q = some (6,[d,c,f,a]))
    (truePart : parts (fixed entries heads) q r 7 fs = true) :
    r = packNode 3 [c] := by
  cases fs with
  | cons _ _ => cases truePart
  | nil =>
    change NumberedWindowMarkRootAlgorithm.bottom q r = true at truePart
    rw [exact_AuxiliaryBottomPart q r d c f a hq] at truePart
    simp only [NumberedWindowMarkRootAlgorithm.guarded,Bool.and_eq_true,beq_iff_eq] at truePart
    exact truePart.2.2.symm

/-- The exact originally calibrated root leaves can be made transparent
at an auxiliary source. Non-auxiliary raw inputs and the original
actual leaves for beta and bottom retain the same calls. -/
theorem exact_AuxiliaryLeafFit (entries : Entries) (heads : List Nat)
    (leaf : Nat → Program 3) (old : LeafFit (fixed entries heads) leaf) :
    LeafFit (fixed entries heads) (leafAtAuxiliary leaf) := by
  intro tag q cert r fs parsed
  change evaluate (leafAtAuxiliary leaf tag) (tape q cert r) = _
  have actual := old tag q cert r fs parsed
  rcases auxValue q cert r with aux | ⟨aux,d,c,f,a,hq⟩
  · simp only [leafAtAuxiliary]
    split
    · rwa [evalBranch,aux,if_pos rfl]
    · split
      · rwa [evalBranch,aux,if_pos rfl]
      · split
        · rwa [evalBranch,aux,if_pos rfl]
        · exact actual
  · simp only [leafAtAuxiliary]
    split
    · rename_i low
      rw [evalBranch,aux,if_neg (by decide : (1 : Nat) ≠ 0),
        exact_AuxiliaryRejectsOtherRootParts entries heads q r d c f a tag fs hq low]
      rfl
    · split
      · rename_i eq
        subst tag
        rw [evalBranch,aux,if_neg (by decide : (1 : Nat) ≠ 0)]
        apply addCheck (leaf 6) functionLambdaHeader (tape q cert r) _ actual
        intro yes
        obtain ⟨row,hf⟩ := betaObservation entries heads q r d c f a fs hq yes
        exact functionHeaderOf q cert r d c f a row hq hf
      · split
        · rename_i eq
          subst tag
          rw [evalBranch,aux,if_neg (by decide : (1 : Nat) ≠ 0)]
          apply addCheck (leaf 7) targetBottom (tape q cert r) _ actual
          intro yes
          exact targetValue q cert r d c f a hq (bottomObservation entries heads q r d c f a fs hq yes)
        · exact actual

#print axioms exact_AuxiliaryLeafFit
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxRootLeafFitProof
