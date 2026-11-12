module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthStepProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem cellRecover (count role typ raw jobs mark rawChild : OTerm alpha)
 (hm : Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild count jobs))) :
 Nonempty (Derivation body Delta (graph5 decorate mark count role typ raw rawChild)) := by
 let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
 have hlook : Nonempty (Derivation body Delta
   (programGraph (.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4]) rawChild xs)) :=
   binaryValue InternalRawListRecursion.lookup (.projection 0) (.projection 4) rawChild count jobs xs
     hl (projectionValue 0 xs) (projectionValue 4 xs)
 apply compositionRecover decorate ![.projection 0,.projection 1,.projection 2,.projection 3,.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4] ] mark xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawChild Fin.elim0))))) hm
 intro i
 exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
   (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
     (Fin.cases hlook (fun k => Fin.elim0 k))))) i

theorem cellValue (count role typ raw jobs mark rawChild : OTerm alpha)
 (hm : Nonempty (Derivation body Delta (graph5 decorate mark count role typ raw rawChild)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild count jobs))) :
 Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)) := by
 let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
 have hlook : Nonempty (Derivation body Delta
   (programGraph (.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4]) rawChild xs)) :=
   binaryValue InternalRawListRecursion.lookup (.projection 0) (.projection 4) rawChild count jobs xs
     hl (projectionValue 0 xs) (projectionValue 4 xs)
 apply compositionValue decorate ![.projection 0,.projection 1,.projection 2,.projection 3,.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4] ] mark xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawChild Fin.elim0))))) hm
 intro i
 exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
   (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
     (Fin.cases hlook (fun k => Fin.elim0 k))))) i

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

theorem scanAppendRecover (count previous role typ raw jobs mark singleton output : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 scan previous count role typ raw jobs)))
 (hs : Nonempty (Derivation body Delta (graph5 scan output (suc count) role typ raw jobs)))
 (hm : Nonempty (Derivation body Delta (graph5 cell mark count role typ raw jobs)))
 (hc : Nonempty (Derivation body Delta (consGraph singleton mark z))) :
 Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append output previous singleton)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons count (Fin.cons jobs Fin.elim0)
 apply programCases InternalRawListRecursion.lookup xs _
 intro beta rho Theta rawChild hrho hlookup
 simp only [graph2Rename]
 let xx : Fin 2 → OTerm beta := Fin.cons (count.relabel rho) (Fin.cons (jobs.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hlookup
 have hp' := renameInto hp rho Theta hrho
 have hs' := renameInto hs rho Theta hrho
 have hm' := renameInto hm rho Theta hrho
 have hc' := renameInto hc rho Theta hrho
 simp only [graph5Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hp' hs' hm'
 rw [InternalListCodecSupportProof.consGraphRename] at hc'
 simp only [InternalTagArithmeticSyntaxProof.zRelabel] at hc'
 exact scanAppendAtLookup (count.relabel rho) (previous.relabel rho) (role.relabel rho)
   (typ.relabel rho) (raw.relabel rho) (jobs.relabel rho) (mark.relabel rho)
   (singleton.relabel rho) (output.relabel rho) rawChild hp' hs' hm' hc' hlookup

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthStepProof
