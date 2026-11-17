module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryIteration.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunGraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z)
open InternalAcceptanceConjunctionProof (constantZeroValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem recover (E : Program 3) (count pool seed parameter out singleton : OTerm alpha)
    (hsingle : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleton seed z)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run E) out count pool seed parameter))) :
    Nonempty (Derivation body Delta (graph4 (PrimaryIteration.iterate E) out count pool singleton parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![count,pool,seed,parameter]
  let singleP : Program 4 := .composition InternalListCodec.consCode
    ![.projection 2,InternalAcceptance.constantZero 4]
  have hsc := binaryValue InternalListCodec.consCode (.projection 2)
    (InternalAcceptance.constantZero 4) singleton seed z xs hsingle
    (projectionValue 2 xs) (constantZeroValue xs)
  apply compositionRecover (PrimaryIteration.iterate E)
    ![.projection 0,.projection 1,singleP,.projection 3] out xs
    ![count,pool,singleton,parameter] hr
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases hsc (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k)))) i
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunGraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryMetadataPreservation.RunGraphProof
