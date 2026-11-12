module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
def ActualSpinePrefix : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert childCert parameter fn targetFn arg d e arrow : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow fn)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow targetFn)) →
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left d arg)) →
 Nonempty (Derivation body Delta (graph4 application s d e fn arg)) →
 Nonempty (Derivation body Delta (graph4 application t d e targetFn arg)) →
 Nonempty (Derivation body Delta (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  (numeral 1) fn targetFn childCert parameter)) →
 Nonempty (Derivation body Delta (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  (numeral 1) s t cert parameter))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixTargets
