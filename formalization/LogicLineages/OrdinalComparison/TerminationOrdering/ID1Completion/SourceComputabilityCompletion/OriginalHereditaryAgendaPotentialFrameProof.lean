module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialFrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalListCodecSupportProof (consGraph)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalAdditionLawsProof (add)
open OriginalHereditaryAgendaPotential
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceBranchProof
theorem visitCost (frame job branching value : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hv : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.jobBudget value job branching))) :
 Nonempty (Derivation body Delta (graph2 frameCost (add value value) frame branching)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons frame (Fin.cons branching Fin.elim0)
 have hl := unaryValue InternalUnpair.left (.projection 0) z frame xs (pairLeft frame z job hf) (projectionValue 0 xs)
 have hr := unaryValue InternalUnpair.right (.projection 0) job frame xs (pairRight frame z job hf) (projectionValue 0 xs)
 let p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 2 := .composition OriginalHereditaryBudgetSum.jobBudget ![rightOf (.projection 0),.projection 1]
 have hp : Nonempty (Derivation body Delta (programGraph p value xs)) :=
   binaryValue OriginalHereditaryBudgetSum.jobBudget (rightOf (.projection 0)) (.projection 1)
     value job branching xs hv hr (projectionValue 1 xs)
 apply zeroBranchIntro (leftOf (.projection 0)) _ _ (add value value) xs hl
 exact binaryValue InternalArithmeticPrograms.addition p p (add value value) value value xs
   (InternalArithmeticProgramsSupportProof.additionValue value value) hp hp

theorem returnCost (frame payload branching : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (suc z) payload))) :
 Nonempty (Derivation body Delta (graph2 frameCost (suc z) frame branching)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons frame (Fin.cons branching Fin.elim0)
 have hl := unaryValue InternalUnpair.left (.projection 0) (suc z) frame xs
   (pairLeft frame (suc z) payload hf) (projectionValue 0 xs)
 exact successorBranchIntro (leftOf (.projection 0)) _ (OriginalRawSyntaxTransport.constant 2 1) (suc z) z xs hl
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 1 xs)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialFrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialFrameProof
