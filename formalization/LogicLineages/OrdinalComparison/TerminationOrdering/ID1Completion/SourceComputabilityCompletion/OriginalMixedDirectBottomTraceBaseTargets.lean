module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceBaseTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Actual empty original path recognition exposes exact direct-bottom
certificate provenance; no arbitrary root rule is admitted by the base. -/
def ActualNilBase : Prop := ∀ (source : Program 2) (leaf : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)) →
 Nonempty (Derivation body Delta (graph4 (OriginalMixedDirectBottomTrace.recognizes source leaf) (suc z) s t cert parameter)) →
 Nonempty (Derivation body Delta
  (graph2 source (suc z) s parameter ⊓
   (graph4 leaf (suc z) s t cert parameter ⊓
    graph1 OriginalTransparentDirectBottom.certificateCode cert s)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceBaseTargets
