module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalListCodecSupportProof (consGraph)
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalAdditionLawsProof (add)
open OriginalHereditaryBudgetSum
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem jobValue (job branching weight value : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (hv : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget value weight branching))) :
 Nonempty (Derivation body Delta (graph2 jobBudget value job branching)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons job (Fin.cons branching Fin.elim0)
 exact binaryValue OriginalHereditaryFuelProgram.budget
   (.composition OriginalHereditaryFuelProgram.weight (fun _ : Fin 1 => .projection 0)) (.projection 1)
   value weight branching xs hv
   (unaryValue OriginalHereditaryFuelProgram.weight (.projection 0) weight job xs hw (projectionValue 0 xs))
   (projectionValue 1 xs)

theorem jobRecover (job branching weight value : OTerm alpha)
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (hv : Nonempty (Derivation body Delta (graph2 jobBudget value job branching))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget value weight branching)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons job (Fin.cons branching Fin.elim0)
 exact binaryRecover OriginalHereditaryFuelProgram.budget
   (.composition OriginalHereditaryFuelProgram.weight (fun _ : Fin 1 => .projection 0)) (.projection 1)
   value weight branching xs hv
   (unaryValue OriginalHereditaryFuelProgram.weight (.projection 0) weight job xs hw (projectionValue 0 xs))
   (projectionValue 1 xs)

theorem nilValue (branching : OTerm alpha) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum z z branching)) :=
 InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 1 0) sumStep z (Fin.cons branching Fin.elim0)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 (Fin.cons branching Fin.elim0))

theorem consValue (jobs job tail branching value total : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs job tail)))
 (hv : Nonempty (Derivation body Delta (graph2 jobBudget value job branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total tail branching))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum (add value total) jobs branching)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons job (Fin.cons total (Fin.cons branching Fin.elim0))
 apply InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 1 0) sumStep
   jobs job tail total (add value total) (Fin.cons branching Fin.elim0) hc ht
 exact binaryValue InternalArithmeticPrograms.addition
   (.composition jobBudget ![.projection 0,.projection 2]) (.projection 1)
   (add value total) value total xs (InternalArithmeticProgramsSupportProof.additionValue value total)
   (binaryValue jobBudget (.projection 0) (.projection 2) value job branching xs hv
     (projectionValue 0 xs) (projectionValue 2 xs))
   (projectionValue 1 xs)

theorem consEquation (jobs job tail branching value total out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs job tail)))
 (hv : Nonempty (Derivation body Delta (graph2 jobBudget value job branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total tail branching)))
 (ho : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum out jobs branching))) :
 Nonempty (Derivation body Delta (eqn out (add value total))) :=
 valueUnique OriginalHereditaryBudgetSum.sum out (add value total) (Fin.cons jobs (Fin.cons branching Fin.elim0))
   ho (consValue jobs job tail branching value total hc hv ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
