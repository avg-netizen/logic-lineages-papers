module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtension
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors

/-- One connected runtime extension. The supplied source Object retains its
original raw payload and context; the extended context is the ORIGINAL cons
graph, and both parameters have the SAME outer context. The independently
supplied body payload is packaged only in that extended context.

The names lambdaObject and lambdaRaw identify intended later consumers, not
a lambda-shape premise or conclusion. No relation between lambdaRaw and
bodyRaw, no source typing and no computability assertion is included. -/
def Recovered {alpha : Type}
    (context d lambdaObject bodyRaw gammaCode lambdaRaw parameter extendedGammaCode
      bodyParameter bodyObject : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing lambdaObject gammaCode lambdaRaw ⊓
    (graph2 InternalListCodec.consCode extendedGammaCode d gammaCode ⊓
      (graph2 InternalPairing.pairing parameter context gammaCode ⊓
        (graph2 InternalPairing.pairing bodyParameter context extendedGammaCode ⊓
          graph2 InternalPairing.pairing bodyObject extendedGammaCode bodyRaw)))

/-- Open the supplied ORIGINAL Object internally and construct all companion
runtime witnesses using original graph totality. Neither its pair shape nor
its original Gamma/raw coordinates are external hypotheses. The continuation
receives those coordinates together with the SAME source Object, outer
context, arbitrary type code and independent supplied body payload.

This is symbolic context-code transport only. It has no evaluation/reflection
premise and does not identify a runtime code with a native Lean context. -/
def RuntimeExtension : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (context d lambdaObject bodyRaw : OTerm alpha) (psi : Formula alpha),
  (∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)),
    (∀ h ∈ Gamma, h.relabel j ∈ Delta) →
    ∀ gammaCode lambdaRaw parameter extendedGammaCode bodyParameter bodyObject : OTerm beta,
    Nonempty (Derivation body Delta
      (Recovered (context.relabel j) (d.relabel j) (lambdaObject.relabel j)
        (bodyRaw.relabel j) gammaCode lambdaRaw parameter extendedGammaCode
        bodyParameter bodyObject)) →
    Nonempty (Derivation body Delta (psi.relabel j))) →
  Nonempty (Derivation body Gamma psi)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtension
