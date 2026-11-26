module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSplitSideIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalOpenOriginScanIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountReflexiveProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedPartitionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalChangedSideFromScratchProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalDirectInsertedScanTargets (loopAccept)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (tripleTerm)
open NumberedWindowInternalDirectSplitSideIntroProof
open NumberedWindowInternalLiteralCountReflexiveProof (exact_LiteralObserverReflexivity)
open NumberedWindowInternalDirectTargetMapLocalIntroProof (exact_OpenRawTargetProjectionIntro)
open NumberedWindowInternalOpenOriginScanIntroProof (exact_OpenOriginRawScanIntro)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)

abbrev Body (i : Program 1) (r : Program 3) (c : Nat) := sourceBody (literalData i r) c

/-- Actual paid physical scratch reports of one changed component.
The new destination scratch is the EXACT kept/inserted projection
append, so its certificate's own observer uses checked reflexivity. -/
structure ScratchSide (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} (Γ : List (Formula α))
    (s removed ds dt dk dd da projected srcJoin head tail : OTerm α) : Prop where
  sourceParse : Report (B := Body i r c) (Γ := Γ) parser (suc ds) ![s]
  removedParse : Report (B := Body i r c) (Γ := Γ) parser (suc dd) ![removed]
  sourceTyped : Report (B := Body i r c) (Γ := Γ) (typedScratch i) (suc z) ![ds]
  targetTyped : Report (B := Body i r c) (Γ := Γ) (typedScratch i) (suc z) ![dt]
  removedCons : Nonempty (Derivation (Body i r c) Γ (consGraph dd head tail))
  sourceAppend : Report (B := Body i r c) (Γ := Γ) append srcJoin ![dk,dd]
  sourceCount : Report (B := Body i r c) (Γ := Γ) permutation (suc z) ![ds,srcJoin]
  targetAppend : Report (B := Body i r c) (Γ := Γ) append dt ![dk,projected]
  projection : Report (B := Body i r c) (Γ := Γ) scratchTargets (suc projected) ![da]
  rows : Nonempty (Derivation (Body i r c) Γ (loopAccept r da removed))

/-- Build the actual fresh original tag-5 certificate of this changed
component, with exact original raw parser repacks for kept, inserted
and destination. The occupied removed code is already fixed by scan. -/
theorem exact_LiteralChangedSideFromScratch (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)}
    (s removed ds dt dk dd da projected srcJoin head tail kept inserted dst : OTerm α)
    (p : ScratchSide i r c Γ s removed ds dt dk dd da projected srcJoin head tail)
    (keep : Report (B := Body i r c) (Γ := Γ) parser (suc dk) ![kept])
    (rows : Report (B := Body i r c) (Γ := Γ) parser (suc da) ![inserted])
    (dest : Report (B := Body i r c) (Γ := Γ) parser (suc dt) ![dst]) :
    Nonempty (Derivation (Body i r c) Γ
      (certificate (literalData i r) true c s dst (tripleTerm 5 kept removed inserted))) := by
  let B := Body i r c
  have rawProjection := exact_OpenRawTargetProjectionIntro B α Γ inserted da projected rows p.projection
  have scan := exact_OpenOriginRawScanIntro r B α Γ inserted da removed rows p.rows
  apply exact_LiteralChangedSideCertificate i r c s dst kept removed inserted ds dt dk dd projected
    srcJoin dt head tail
  exact ⟨⟨⟨p.sourceParse,dest,p.removedParse⟩,p.sourceTyped,p.targetTyped,p.removedCons⟩,
    keep,rawProjection,p.sourceAppend,p.targetAppend,p.sourceCount,
    exact_LiteralObserverReflexivity B α Γ dt,scan⟩

#print axioms exact_LiteralChangedSideFromScratch
end LogicLineages.PersistentMarking.NumberedWindowInternalChangedSideFromScratchProof
