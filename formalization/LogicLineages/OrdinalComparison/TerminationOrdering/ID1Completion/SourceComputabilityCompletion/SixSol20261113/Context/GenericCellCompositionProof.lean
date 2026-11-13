module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.GenericCellCompositionProof
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
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

attribute [local irreducible] programGraph

def replaceLast (P : Program 5) : Program 5 := .composition P
  ![.projection 0,.projection 1,.projection 2,.projection 3,
    .composition InternalRawListRecursion.lookup ![.projection 0,.projection 4] ]

theorem recover (P : Program 5) (count role typ raw jobs mark rawChild : OTerm alpha)
 (hm : Nonempty (Derivation body Delta (graph5 (replaceLast P) mark count role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild count jobs))) :
 Nonempty (Derivation body Delta (graph5 P mark count role typ raw rawChild)) := by
 let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
 have hlook : Nonempty (Derivation body Delta
   (programGraph (.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4]) rawChild xs)) :=
   binaryValue InternalRawListRecursion.lookup (.projection 0) (.projection 4) rawChild count jobs xs
     hl (projectionValue 0 xs) (projectionValue 4 xs)
 apply compositionRecover P ![.projection 0,.projection 1,.projection 2,.projection 3,.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4] ] mark xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawChild Fin.elim0))))) hm
 intro i
 exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
   (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
     (Fin.cases hlook (fun k => Fin.elim0 k))))) i

theorem value (P : Program 5) (count role typ raw jobs mark rawChild : OTerm alpha)
 (hm : Nonempty (Derivation body Delta (graph5 P mark count role typ raw rawChild)))
 (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawChild count jobs))) :
 Nonempty (Derivation body Delta (graph5 (replaceLast P) mark count role typ raw jobs)) := by
 let xs : Fin 5 → OTerm alpha := Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))
 have hlook : Nonempty (Derivation body Delta
   (programGraph (.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4]) rawChild xs)) :=
   binaryValue InternalRawListRecursion.lookup (.projection 0) (.projection 4) rawChild count jobs xs
     hl (projectionValue 0 xs) (projectionValue 4 xs)
 apply compositionValue P ![.projection 0,.projection 1,.projection 2,.projection 3,.composition InternalRawListRecursion.lookup ![.projection 0,.projection 4] ] mark xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawChild Fin.elim0))))) hm
 intro i
 exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
   (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
     (Fin.cases hlook (fun k => Fin.elim0 k))))) i


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.GenericCellCompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.GenericCellCompositionProof
