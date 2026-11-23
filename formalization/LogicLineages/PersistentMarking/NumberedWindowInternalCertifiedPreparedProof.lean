module
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetRecombineTotalityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginBothRemovedNonemptyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedPartitionProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (Pr SplitCases)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalOriginKeptSplitTargets (evidence piece)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (App)
open NumberedWindowInternalChangedSideFromScratchProof (Body)
open NumberedWindowInternalScratchSideSeedProof (ScratchSideSeed)
open NumberedWindowInternalCertifiedTwoSideFinishProof (exact_OriginalCertifiedTwoSideFinish)
open NumberedWindowInternalDirectTargetRecombineTotalityProof (exact_LiteralTargetRecombineTotal)
open NumberedWindowInternalOriginBothRemovedNonemptyProof (exact_OpenOriginBothRemovedNotNil)
open NumberedWindowInternalLiteralTypedPartitionProof (exact_LiteralTypedParts)
open NumberedWindowInternalCertifiedPreparedTargets

/-- At actual chosen target appends, compute the exact target partition,
supply both true typed sides, rule out no strict component, and finish
the original unchanged/changed certificate cases. -/
theorem exact_OriginalCertifiedPreparedAtAppends (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)}
    (a b v ls rs t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin : OTerm α)
    (w : Fin 8 → OTerm α) (goal : Formula α)
    (known : Known i r c Γ a b v ls rs t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin w)
    (tl tr join : OTerm α)
    (apL : Pr (literalData i r) c Γ (App (w 0) pL tl))
    (apR : Pr (literalData i r) c Γ (App (w 2) pR tr))
    (ap : Pr (literalData i r) c Γ (App tl tr join))
    (next : SplitCases (literalData i r) c permutation Γ a b v goal) :
    Pr (literalData i r) c Γ goal := by
  let B := Body i r c
  obtain ⟨ev⟩ := known.allocation
  let srcL := Derivation.conjunctionLeft ev
  let base := Derivation.conjunctionRight ev
  let srcR := Derivation.conjunctionLeft base
  let keep := Derivation.conjunctionLeft (Derivation.conjunctionRight base)
  have count := exact_LiteralTargetRecombineTotal t kept p (w 0) (w 2) pL pR (w 6)
    pJoin oldJoin tl tr join known.oldAppend known.oldCount ⟨Derivation.conjunctionLeft keep⟩
    known.bothProjected ⟨Derivation.conjunctionRight keep⟩ known.projectedCount apL apR ap
  obtain ⟨admitL,admitR⟩ := exact_LiteralTypedParts i t tl tr join known.targetTyped ap count
  have left : ScratchSideSeed i r c Γ a rawDL ls tl (w 0) (w 1) rowsL pL (w 4) :=
    ⟨known.leftParse,known.pools.leftParsed,known.leftTyped,admitL,
      ⟨Derivation.conjunctionLeft srcL⟩,⟨Derivation.conjunctionRight srcL⟩,
      apL,known.leftProj,known.leftRows⟩
  have right : ScratchSideSeed i r c Γ b rawDR rs tr (w 2) (w 3) rowsR pR (w 5) :=
    ⟨known.rightParse,known.pools.rightParsed,known.rightTyped,admitR,
      ⟨Derivation.conjunctionLeft srcR⟩,⟨Derivation.conjunctionRight srcR⟩,
      apR,known.rightProj,known.rightRows⟩
  have changed := exact_OpenOriginBothRemovedNotNil B α Γ d dh dTail (w 1) (w 3) (w 7)
    known.removedCons known.pools.appended known.pools.count
  exact exact_OriginalCertifiedTwoSideFinish i r c a b v goal rawDL rawDR ls rs tl tr
    (w 0) (w 2) (w 1) (w 3) rowsL rowsR pL pR (w 4) (w 5) t join left right
    changed known.targetParse ap count next

#print axioms exact_OriginalCertifiedPreparedAtAppends
end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedProof
