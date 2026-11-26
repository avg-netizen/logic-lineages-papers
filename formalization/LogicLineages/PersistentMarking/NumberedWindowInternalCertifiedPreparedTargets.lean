module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedPartitionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalProjectedCountInductionTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedTwoSideFinishProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginKeptSplitTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalOriginScanInductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedTargets
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalLiteralTypedPartitionProof (Typed)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalProjectedCountInductionTargets (project compared)
open NumberedWindowInternalOriginKeptSplitTargets (evidence)
open NumberedWindowInternalOriginScanInductionTargets (Pools)
open NumberedWindowInternalRawUnionFromEquivalentPartsProof (App Cmp)
open NumberedWindowInternalChangedSideFromScratchProof (Body)

/-- All original physical premises already opened at one context. No new
side destination, raw replacement, or split continuation is assumed. -/
structure Known (i : Program 1) (r : Program 3) (c : Nat) {α : Type} (Γ : List (Formula α))
    (a b v l s t kept d dh dTail removed rawDL rawDR p fullRows rowsL rowsR pL pR pJoin oldJoin : OTerm α)
    (w : Fin 8 → OTerm α) : Prop where
  leftParse : Pr (literalData i r) c Γ (unary parser (suc l) a)
  rightParse : Pr (literalData i r) c Γ (unary parser (suc s) b)
  targetParse : Pr (literalData i r) c Γ (unary parser (suc t) v)
  leftTyped : Pr (literalData i r) c Γ (Typed i l)
  rightTyped : Pr (literalData i r) c Γ (Typed i s)
  targetTyped : Pr (literalData i r) c Γ (Typed i t)
  removedCons : Pr (literalData i r) c Γ (consGraph d dh dTail)
  allocation : Pr (literalData i r) c Γ (evidence l s kept d w)
  pools : Pools (Body i r c) Γ removed d rawDL rawDR (w 1) (w 3) (w 7)
  leftRows : Pr (literalData i r) c Γ (loopAccept r rowsL rawDL)
  rightRows : Pr (literalData i r) c Γ (loopAccept r rowsR rawDR)
  leftProj : Pr (literalData i r) c Γ (project pL rowsL)
  rightProj : Pr (literalData i r) c Γ (project pR rowsR)
  bothProjected : Pr (literalData i r) c Γ (App pL pR pJoin)
  projectedCount : Pr (literalData i r) c Γ (Cmp p pJoin)
  oldAppend : Pr (literalData i r) c Γ (App kept p oldJoin)
  oldCount : Pr (literalData i r) c Γ (Cmp t oldJoin)

end LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedPreparedTargets
