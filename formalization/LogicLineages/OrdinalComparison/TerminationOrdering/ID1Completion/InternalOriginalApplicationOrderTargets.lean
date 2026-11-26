module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedBoundedDescentNormalizer
open InternalGraphComposition (OTerm)

/-- Internal monotonicity of the ORIGINAL raw application number. Both
applications retain the same explicit domain, codomain and arrow code.
The actual child left-field graphs are essential: application drops those
outer type fields. No semantic calibration, source validity, canonicality,
recursive invariant or native numerical inference is assumed. -/
def ActualOriginalApplicationCodeMonotonicity : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (arrow domain codomain function argument function' argument' parent parent' : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 InternalListCodec.consCode arrow domain codomain ⊓
      (graph1 InternalUnpair.left arrow function ⊓
        (graph1 InternalUnpair.left arrow function' ⊓
          (graph1 InternalUnpair.left domain argument ⊓
            (graph1 InternalUnpair.left domain argument' ⊓
              (graph4 application parent domain codomain function argument ⊓
                (graph4 application parent' domain codomain function' argument' ⊓
                  (atMost function' function ⊓ atMost argument' argument)))))))).imp
      (atMost parent' parent)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderTargets
