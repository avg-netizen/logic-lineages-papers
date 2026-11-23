module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptChooseSideProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptLeftFinishProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseSuccessCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptCompleteProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraphRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalOriginKeptSplitTargets
open NumberedWindowInternalOriginKeptInductionSyntaxProof (splitRename A C)
open NumberedWindowInternalOriginKeptInductionProof (exact_OriginalKeptSplitInduction)
open NumberedWindowInternalOriginKeptChooseSideProof (exact_OriginalMoveOneKeptFromLeft)
open NumberedWindowInternalOriginKeptRightAdapterProof (LeftOpenedSupply)
open NumberedWindowInternalOriginKeptLeftFinishProof (Held exact_OriginalKeptLeftFinish)
open NumberedWindowInternalLiteralScratchEraseSuccessCasesProof (successCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Genuine selected original eraser and exact left graph reconstruction
supply the left-origin move without any separate arithmetic premise. -/
theorem exact_OriginalKeptMoveLeft (B : Positive (Fin 1)) : LeftOpenedSupply B := by
  intro α Γ l r k h t d e w kc dc old member
  apply successCases (w 1) h (splitExists l r k d) member
  intro β j Δ rest rebuilt keep cell cmp
  rw [splitRename]
  let W : Fin 8 → OTerm β := fun v => (w v).relabel j
  have originals : Nonempty (Derivation B Δ (evidence (l.relabel j) (r.relabel j) (t.relabel j) (e.relabel j) W)) := by
    simpa only [evidence,piece,conjunctionRename,programRename,binaryInputsRename,sucRelabel,zRelabel,W] using
      renameInto old j Δ keep
  have k' := renameInto kc j Δ keep
  have d' := renameInto dc j Δ keep
  rw [consGraphRename] at k' d'
  apply exact_OriginalKeptLeftFinish (l.relabel j) (r.relabel j) (k.relabel j) (d.relabel j)
    (t.relabel j) (e.relabel j) (h.relabel j) rest rebuilt W
  exact ⟨originals,cmp,k',d',cell⟩

/-- Every actual original balance of these symbolic tapes gives the
four exact ordered origin reports. The single-erasure move is paid
inside the actual object proof, not supplied by the caller. -/
theorem exact_OriginalKeptSplit (l r k d src dst : OTerm α)
    (srcRead : Nonempty (Derivation B Γ (A l r src)))
    (dstRead : Nonempty (Derivation B Γ (A k d dst)))
    (bal : Nonempty (Derivation B Γ (C src dst))) :
    Nonempty (Derivation B Γ (splitExists l r k d)) :=
  exact_OriginalKeptSplitInduction
    (exact_OriginalMoveOneKeptFromLeft (exact_OriginalKeptMoveLeft B)) l r k d src dst srcRead dstRead bal

#print axioms exact_OriginalKeptMoveLeft
#print axioms exact_OriginalKeptSplit
end LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptCompleteProof
