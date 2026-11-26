module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanLengthTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanRecoverProof
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
open OriginalContextInsertion (lengthGraph length)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.decorate OriginalHereditaryAnnotatedExpansion.scan

theorem scanFromAll (role typ raw jobs output count : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph4 decorateAll output role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs))) :
 Nonempty (Derivation body Delta (graph5 scan output count role typ raw jobs)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))
 apply compositionRecover scan _ output xs
   (Fin.cons count (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0))))) ha
 intro i
 exact Fin.cases
   (unaryValue length (.projection 3) count jobs xs hl (projectionValue 3 xs))
   (Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
     (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k))))) i


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanRecoverProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanRecoverProof
