module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePositiveTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
/-- Every actual raw encoding tree has a positive node count, including
malformed leaves. No source/type, native calibration or positivity premise. -/
def Positive : Prop := ∀ (body : PositiveArithmeticOperators.Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (input count : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta ((graph1 OriginalStructuralNodeSize.raw count input).imp
    (InternalLessThan.strictLess InternalTagArithmeticSyntaxProof.z count)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizePositiveTargets
