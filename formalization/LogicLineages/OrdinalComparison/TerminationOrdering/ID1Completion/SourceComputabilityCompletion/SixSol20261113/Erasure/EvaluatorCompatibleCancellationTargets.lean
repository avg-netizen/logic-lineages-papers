module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyCanonicalPreservationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleCancellationTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Context Context.EvaluatorKeyPut
/-- CONDITIONAL cancellation for the SAME explicitly NEW original Object
wrapper. The only semantic assumption is the SAME uniform internal retained-R
compatibility used in constructor/canonical preservation. In particular no
Same E of erased payloads, parent preservation, fixedness, or equality of
wrapper outputs is supplied. All shifted/folded/erased source and parameter
metadata must be recovered from the literal operations. Arbitrary d follows
the existing original raw weakening/cancellation scope, not native typing.
This is not unconditional Object cancellation or global shift-invariance. -/
def ActualCompatibleCancellation : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3),
 Context.EvaluatorKeyCanonicalPreservationDefinitions.Compatible p H G W →
 ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (input raw gamma context parameter d shifted canonicalShift erased erasedRaw out originalOut : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing input gamma raw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
 Nonempty (Derivation body Delta (Domain p H G W raw parameter)) →
 Nonempty (Derivation body Delta (graph2 OriginalRawObjectTransport.shiftObjectRaw shifted d input)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) canonicalShift context shifted)) →
 Nonempty (Derivation body Delta (graph1 OriginalRawObjectTransport.eraseObjectRaw erased canonicalShift)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.right erasedRaw erased)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) out context erased)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) originalOut context input)) →
 Nonempty (Derivation body Delta (equal out originalOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorCompatibleCancellationTargets
