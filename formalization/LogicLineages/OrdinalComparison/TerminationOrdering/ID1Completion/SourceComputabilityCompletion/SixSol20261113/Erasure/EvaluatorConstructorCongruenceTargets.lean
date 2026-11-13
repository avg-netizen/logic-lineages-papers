module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions
open EvaluatorConstructorCongruenceDefinitions
/-- CONDITIONAL original application congruence, not canonical preservation.
Both parent source tests and actual typed constructor coordinates are retained.
No parent evaluator equality or deletion-cell agreement is assumed. -/
def ActualApplication : Prop :=
 ∀ (R : Program 2) (H G : Program 1) (M W : Program 2),
 UniformRetainedCompatibility R H G M W →
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right fnLeft fnRight argLeft argRight arrow domain codomain fpLeft fpRight apLeft apRight parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)) →
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fpLeft apLeft fnLeft argLeft left)) →
 Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow domain codomain fpRight apRight fnRight argRight right)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W fnLeft fnRight parameter)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W argLeft argRight parameter)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))
/-- CONDITIONAL lambda congruence at the literal changed child parameter.
The common binder/domain and codomain are retained. The uniform rule above,
not a fixed-parameter native calibration, covers all recursive deletions. -/
def ActualLambda : Prop :=
 ∀ (R : Program 2) (H G : Program 1) (M W : Program 2),
 UniformRetainedCompatibility R H G M W →
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (left right childLeft childRight domain codomain parameter childParameter c gamma childGamma : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) left parameter)) →
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) right parameter)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childGamma domain gamma)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)) →
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor left domain codomain childLeft)) →
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor right domain codomain childRight)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left codomain childLeft)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left codomain childRight)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W childLeft childRight childParameter)) →
 Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCongruenceTargets
