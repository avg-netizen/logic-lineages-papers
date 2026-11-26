module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationPackedTagProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rawTag (input typ raw tag : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input typ raw)))
 (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag input))) :
 Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag tag raw)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons input Fin.elim0
 have hr := unaryValue InternalUnpair.right (.projection 0) raw input xs (pairRight input typ raw hp) (projectionValue 0 xs)
 exact unaryRecover InternalUnpair.left (rightOf (.projection 0)) tag raw xs ht hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationPackedTagProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationPackedTagProof
