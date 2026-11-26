module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalTagArithmeticSyntaxProof (z suc)
/-- Exact structural peeling and selectors. No endpoint premise. -/
def ActualFields : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (d e arrow s t a certificate k lifted : OTerm alpha),
 Nonempty (Derivation body Delta (taggedEdge d e arrow s t a certificate k)) →
 Nonempty (Derivation body Delta (graph4 edgeLift lifted d e a certificate)) →
 Nonempty (Derivation body Delta (graph1 InternalApplicationStepPeel.structuralGuard (suc z) lifted ⊓
 (graph1 InternalApplicationStepPeel.functionCode s lifted ⊓
 (graph1 InternalApplicationStepPeel.targetFunctionCode t lifted ⊓
 graph1 InternalApplicationStepPeel.peeledStep k lifted))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionPeelFieldsTargets
