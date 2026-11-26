module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsBoundaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPathCheckerBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof
open InternalArithmeticProgramsSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNe)
open OriginalTypedDecoderInternalBranchProof (sameYesIntro sameNoIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem additionOne (count : OTerm alpha) : Nonempty (Derivation body Delta
 (graph2 InternalArithmeticPrograms.addition (suc count) count (suc z))) := by
 apply outputTransport InternalArithmeticPrograms.addition (InternalAdditionLawsProof.add count (suc z)) (suc count)
   (Fin.cons count (Fin.cons (suc z) Fin.elim0)) _ (additionValue count (suc z))
 exact ⟨trans (addSucc count z) (congSuc (addZero count))⟩

theorem additionTwo (count : OTerm alpha) : Nonempty (Derivation body Delta
 (graph2 InternalArithmeticPrograms.addition (suc (suc count)) count (suc (suc z)))) := by
 apply outputTransport InternalArithmeticPrograms.addition (InternalAdditionLawsProof.add count (suc (suc z))) (suc (suc count))
   (Fin.cons count (Fin.cons (suc (suc z)) Fin.elim0)) _ (additionValue count (suc (suc z)))
 exact ⟨trans (addSucc count (suc z)) (congSuc (trans (addSucc count z) (congSuc (addZero count))))⟩

theorem firstAt (predChild count joined total index value : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition total count (suc predChild))))
 (hp : Nonempty (Derivation body Delta (graph1 InternalEqualityTest.predecessor index total)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value index joined))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.firstSlot value (suc predChild) count joined)) := by
 let xs : Fin 3 → OTerm alpha := ![suc predChild,count,joined]
 have ht : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.totalCount total (suc predChild) count joined)) :=
   binaryValue InternalArithmeticPrograms.addition (.projection 1) (.projection 0) total count (suc predChild) xs ha (projectionValue 1 xs) (projectionValue 0 xs)
 have hi : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.firstIndex index (suc predChild) count joined)) :=
   unaryValue InternalEqualityTest.predecessor OriginalHereditaryResultStackProgram.totalCount index total xs hp ht
 have hv := binaryValue InternalRawListRecursion.lookup OriginalHereditaryResultStackProgram.firstIndex (.projection 2)
   value index joined xs hl hi (projectionValue 2 xs)
 exact InternalPathCheckerBranchProof.nonzeroBranchIntro (.projection 0) (OriginalRawSyntaxTransport.constant 3 0) _
   value (suc predChild) xs (projectionValue 0 xs) ⟨sucNeZero predChild⟩ hv

theorem secondOne (count joined : OTerm alpha) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.secondSlot z (suc z) count joined)) := by
 let xs : Fin 3 → OTerm alpha := ![suc z,count,joined]
 exact sameNoIntro (.projection 0) (OriginalRawSyntaxTransport.constant 3 2) _ (OriginalRawSyntaxTransport.constant 3 0)
   z (suc z) (suc (suc z)) xs (projectionValue 0 xs) (constantValue 2 xs)
   (numeralNe 1 2 (by decide)) (constantValue 0 xs)

theorem secondTwo (count joined value : OTerm alpha)
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value count joined))) :
 Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.secondSlot value (suc (suc z)) count joined)) := by
 let xs : Fin 3 → OTerm alpha := ![suc (suc z),count,joined]
 have hv := binaryValue InternalRawListRecursion.lookup (.projection 1) (.projection 2) value count joined xs hl
   (projectionValue 1 xs) (projectionValue 2 xs)
 exact sameYesIntro (.projection 0) (OriginalRawSyntaxTransport.constant 3 2) _ (OriginalRawSyntaxTransport.constant 3 0)
   value (suc (suc z)) (suc (suc z)) xs (projectionValue 0 xs) (constantValue 2 xs)
   (by simpa only [InternalControlGraphSupportProof.equalEqn] using
     (Nonempty.intro (refl (body:=body) (Gamma:=Delta) (suc (suc z))))) hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
