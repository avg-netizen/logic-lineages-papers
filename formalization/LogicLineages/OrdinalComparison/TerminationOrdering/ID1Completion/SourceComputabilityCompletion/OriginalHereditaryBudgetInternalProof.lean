module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRawListRecursionSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalMultiplicationLawsProof (mul)
open InternalArithmeticProgramsMultiplicationProof (multiplicationValue)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransport (constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryFuelProgram (budget budgetStep)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepValue (depth previous branching : OTerm alpha) :
 Nonempty (Derivation body Delta (graph3 budgetStep (suc (mul branching previous)) depth previous branching)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons depth (Fin.cons previous (Fin.cons branching Fin.elim0))
 have hm : Nonempty (Derivation body Delta (programGraph
   (.composition InternalArithmeticPrograms.multiplication ![.projection 2,.projection 1])
   (mul branching previous) xs)) := binaryValue InternalArithmeticPrograms.multiplication (.projection 2) (.projection 1)
   (mul branching previous) branching previous xs (multiplicationValue branching previous)
   (projectionValue 2 xs) (projectionValue 1 xs)
 exact unaryValue .succ (.composition InternalArithmeticPrograms.multiplication ![.projection 2,.projection 1])
   (suc (mul branching previous)) (mul branching previous) xs
   (successorValue (Fin.cons (mul branching previous) Fin.elim0)) hm

theorem actualZero : OriginalHereditaryBudgetInternalTargets.Zero := by
 intro body alpha Delta branching
 exact recursionZeroValue (constant 1 1) budgetStep (suc z) (Fin.cons branching Fin.elim0)
   (constantValue 1 (Fin.cons branching Fin.elim0))
theorem actualSuccessor : OriginalHereditaryBudgetInternalTargets.Successor := by
 intro body alpha Delta depth branching previous hp
 exact recursionNext (constant 1 1) budgetStep (suc (mul branching previous)) previous depth
   (Fin.cons branching Fin.elim0) hp (stepValue depth previous branching)
theorem actualSuccessorEquation : OriginalHereditaryBudgetInternalTargets.SuccessorEquation := by
 intro body alpha Delta depth branching previous current hp hc
 exact valueUnique budget current (suc (mul branching previous)) (Fin.cons (suc depth) (Fin.cons branching Fin.elim0))
   hc (actualSuccessor body alpha Delta depth branching previous hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetInternalProof
