module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeChildTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (z suc)
/-- All-raw structural child descent, independent of numeric code magnitude,
typing, native calibration and variable-occurrence rank. -/
def UnaryChildStrict : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input child count childCount : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 (arityOf (.projection 0)) (suc z) input ⊓
      (graph1 (firstOf (.projection 0)) child input ⊓
        (graph1 OriginalStructuralNodeSize.raw count input ⊓ graph1 OriginalStructuralNodeSize.raw childCount child))).imp
      (InternalLessThan.strictLess childCount count)))
def BinaryChildrenStrict : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input first second count firstCount secondCount : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 (arityOf (.projection 0)) (suc (suc z)) input ⊓
      (graph1 (firstOf (.projection 0)) first input ⊓
       (graph1 (secondOf (.projection 0)) second input ⊓
        (graph1 OriginalStructuralNodeSize.raw count input ⊓
         (graph1 OriginalStructuralNodeSize.raw firstCount first ⊓ graph1 OriginalStructuralNodeSize.raw secondCount second))))).imp
      (InternalLessThan.strictLess firstCount count ⊓ InternalLessThan.strictLess secondCount count)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeChildTargets
