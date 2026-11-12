module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalListCodecSupportProof (consGraph)
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalAdditionLawsProof (add)
open OriginalHereditaryAgendaPotential
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem nilValue (branching : OTerm alpha) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda z z branching)) :=
 InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 1 0) sumStep z (Fin.cons branching Fin.elim0)
   (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 (Fin.cons branching Fin.elim0))

theorem consValue (jobs job tail branching value total : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs job tail)))
 (hv : Nonempty (Derivation body Delta (graph2 frameCost value job branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda total tail branching))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda (add value total) jobs branching)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons job (Fin.cons total (Fin.cons branching Fin.elim0))
 apply InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 1 0) sumStep
   jobs job tail total (add value total) (Fin.cons branching Fin.elim0) hc ht
 exact binaryValue InternalArithmeticPrograms.addition
   (.composition frameCost ![.projection 0,.projection 2]) (.projection 1)
   (add value total) value total xs (InternalArithmeticProgramsSupportProof.additionValue value total)
   (binaryValue frameCost (.projection 0) (.projection 2) value job branching xs hv
     (projectionValue 0 xs) (projectionValue 2 xs))
   (projectionValue 1 xs)

theorem consEquation (jobs job tail branching value total out : OTerm alpha)
 (hc : Nonempty (Derivation body Delta (consGraph jobs job tail)))
 (hv : Nonempty (Derivation body Delta (graph2 frameCost value job branching)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda total tail branching)))
 (ho : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda out jobs branching))) :
 Nonempty (Derivation body Delta (eqn out (add value total))) :=
 valueUnique OriginalHereditaryAgendaPotential.agenda out (add value total) (Fin.cons jobs (Fin.cons branching Fin.elim0))
   ho (consValue jobs job tail branching value total hc hv ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialRecurrenceProof
