module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanShiftProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanAppendProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRawListRecursionSupportProof
open InternalRecursionGraphStepSyntaxProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc)
open InternalListCodecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAnnotatedExpansion OriginalHereditaryInternalAnnotatedScanDefinitions
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open NarrowScanShiftProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem scanAppendAtLookup (count previous role typ raw jobs mark singleton output rawChild : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 scan previous count role typ raw jobs)))
 (hs : Nonempty (Derivation body Delta (graph5 scan output (suc count) role typ raw jobs)))
 (hm : Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)))
 (hc : Nonempty (Derivation body Delta (consGraph singleton mark z)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild count jobs))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output previous singleton)) := by
 have ht := recursionRecover (OriginalRawSyntaxTransport.constant 4 0) scanStep output previous count
   (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) hp hs
 let xs : Fin 6 → OTerm alpha := Fin.cons count (Fin.cons previous (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))))
 let single : Program 6 := .composition InternalListCodec.consCode ![shiftedCell,OriginalRawSyntaxTransport.constant 6 0]
 have hm' := shiftedCellValue count previous role typ raw jobs mark rawChild hm hl
 have hc' : Nonempty (Derivation body Delta (programGraph single singleton xs)) :=
   binaryValue InternalListCodec.consCode shiftedCell (OriginalRawSyntaxTransport.constant 6 0)
     singleton mark z xs hc hm' (constantValue 0 xs)
 exact binaryRecover InternalApplicationValidityStackAppend.append (.projection 1) single
   output previous singleton xs ht (projectionValue 1 xs) hc'


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanAppendProof
