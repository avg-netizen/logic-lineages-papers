module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.MapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.StepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat)
attribute [local irreducible] programGraph

theorem stepValue (key rest param value out : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (exchange n arity) value key param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value rest))) :
    Nonempty (Derivation body Delta (graph3 (answerStep n arity) out key rest param)) := by
  let xs : Fin 3 → OTerm alpha := ![key,rest,param]
  have he := binaryValue (exchange n arity) (.projection 0) (.projection 2)
    value key param xs hv (projectionValue 0 xs) (projectionValue 2 xs)
  exact binaryValue InternalListCodec.consCode
    (.composition (exchange n arity) ![.projection 0,.projection 2]) (.projection 1)
    out value rest xs hc he (projectionValue 1 xs)

theorem nilValue (param : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 (answerMap n arity) z z param)) :=
  InternalRawListRecursionProof.nilValue (InternalAcceptance.constantZero 1) (answerStep n arity)
    z (Fin.cons param Fin.elim0)
    (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons param Fin.elim0))

theorem consValue (keys key tail param value rest out : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys key tail)))
    (hv : Nonempty (Derivation body Delta (graph2 (exchange n arity) value key param)))
    (hr : Nonempty (Derivation body Delta (graph2 (answerMap n arity) rest tail param)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out value rest))) :
    Nonempty (Derivation body Delta (graph2 (answerMap n arity) out keys param)) :=
  InternalRawListRecursionProof.consValue (InternalAcceptance.constantZero 1) (answerStep n arity)
    keys key tail rest out (Fin.cons param Fin.elim0) hk hr (stepValue n arity key rest param value out hv hc)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.StepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedExchangeEquation.StepProof
