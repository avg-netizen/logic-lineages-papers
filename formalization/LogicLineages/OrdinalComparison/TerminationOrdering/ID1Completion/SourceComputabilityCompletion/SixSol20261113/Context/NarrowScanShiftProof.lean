module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanShiftProof
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
open NarrowScanCellProof NarrowScanCellRecoverProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.decorate

def shiftedCell : Program 6 := .composition decorate
 ![.projection 0,.projection 2,.projection 3,.projection 4,
   .composition InternalRawListRecursion.lookup ![.projection 0,.projection 5] ]

theorem shiftedCellValue (count previous role typ raw jobs mark rawChild : OTerm alpha)
 (hm : Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild count jobs))) :
 Nonempty (Derivation body Delta (programGraph shiftedCell mark (Fin.cons count (Fin.cons previous (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))))))) := by
 let xs : Fin 6 → OTerm alpha := Fin.cons count (Fin.cons previous (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))))
 have hlook : Nonempty (Derivation body Delta
   (programGraph (.composition InternalRawListRecursion.lookup ![.projection 0,.projection 5]) rawChild xs)) :=
   binaryValue InternalRawListRecursion.lookup (.projection 0) (.projection 5) rawChild count jobs xs
     hl (projectionValue 0 xs) (projectionValue 5 xs)
 apply compositionValue decorate
   ![.projection 0,.projection 2,.projection 3,.projection 4,
     .composition InternalRawListRecursion.lookup ![.projection 0,.projection 5] ] mark xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawChild Fin.elim0)))))
   (cellRecover count role typ raw jobs mark rawChild hm hl)
 intro i
 exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 2 xs)
   (Fin.cases (projectionValue 3 xs) (Fin.cases (projectionValue 4 xs)
     (Fin.cases hlook (fun k => Fin.elim0 k))))) i


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanShiftProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanShiftProof
