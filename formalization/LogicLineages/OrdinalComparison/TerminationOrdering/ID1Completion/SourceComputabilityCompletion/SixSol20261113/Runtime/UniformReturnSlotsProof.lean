module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStackProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsPrefixLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof (projectionValue)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof
open InternalAdditionLawsProof (add)
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalResultStackSlotsSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- One child: the one in-range actual lookup is independent of the old stack. -/
theorem oneChild (deletions produced old results first : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc deletions) produced)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first deletions produced))) :
 Nonempty (Derivation body Delta
  (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc z) deletions results ⊓
   graph3 OriginalHereditaryResultStackProgram.secondSlot z (suc z) deletions results)) := by
 have hlookup := OriginalHereditaryDeletionRowsPrefixLookupProof.prefixLookup
   (suc deletions) produced deletions old results first hl
   (InternalCoprimeMultipleBoundedProof.selfLtSucc deletions) ha hv
 exact andIntro
   (firstAt z deletions results (suc deletions) deletions first (additionOne deletions)
     (InternalEqualityTestPredecessorProof.predecessorSuccessor deletions) hlookup)
   (secondOne deletions results)
/-- Two children: both original lookups stay inside the actual produced row. -/
theorem twoChildren (deletions produced old results first second : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc (suc deletions)) produced)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first (suc deletions) produced)))
 (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second deletions produced))) :
 Nonempty (Derivation body Delta
  (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc (suc z)) deletions results ⊓
   graph3 OriginalHereditaryResultStackProgram.secondSlot second (suc (suc z)) deletions results)) := by
 have hbound : Nonempty (Derivation body Delta
   (InternalOriginalOrderSyntaxProof.ltF deletions (suc (suc deletions)))) := by
   apply InternalOriginalOrderProof.actualOriginalOrderIntroduction body alpha Delta deletions
     (suc (suc deletions)) (suc z)
   rw [InternalSourceInversionSupportProof.onEquality]
   exact ⟨trans (addSucc deletions (suc z))
     (congSuc (trans (addSucc deletions z) (congSuc (addZero deletions))))⟩
 have hfirst := OriginalHereditaryDeletionRowsPrefixLookupProof.prefixLookup
   (suc (suc deletions)) produced (suc deletions) old results first hl
   (InternalCoprimeMultipleBoundedProof.selfLtSucc (suc deletions)) ha hf
 have hsecond := OriginalHereditaryDeletionRowsPrefixLookupProof.prefixLookup
   (suc (suc deletions)) produced deletions old results second hl hbound ha hs
 exact andIntro
   (firstAt (suc z) deletions results (suc (suc deletions)) (suc deletions) first
     (additionTwo deletions)
     (InternalEqualityTestPredecessorProof.predecessorSuccessor (suc deletions)) hfirst)
   (secondTwo deletions results second hsecond)
/-- The deletion-row selector is exactly reversal of the available prefix. -/
theorem deletionRow (children deletions results front row : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.front front deletions results)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse row front))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.deletionRow row children deletions results)) := by
 let xs : Fin 3 → OTerm alpha := ![children,deletions,results]
 have hfront : Nonempty (Derivation body Delta
   (graph3 OriginalHereditaryResultStackProgram.deletionFront front children deletions results)) :=
   binaryValue OriginalClassContextAllPositionObserver.front (.projection 1) (.projection 2)
     front deletions results xs hf (projectionValue 1 xs) (projectionValue 2 xs)
 exact unaryValue OriginalTypedArgumentObservations.reverse OriginalHereditaryResultStackProgram.deletionFront
   row front xs hr hfront
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSlotsProof
