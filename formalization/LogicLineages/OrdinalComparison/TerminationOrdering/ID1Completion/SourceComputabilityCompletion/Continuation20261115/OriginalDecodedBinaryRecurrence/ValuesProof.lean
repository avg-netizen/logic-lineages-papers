module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentHeadBranches.Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.ValuesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
variable (n : Nat) (arity : Fin n → Nat)
attribute [local irreducible] programGraph

theorem valueForward (child param value : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param))) :
    Nonempty (Derivation body Delta ((eqn value (numeral 1)).imp
      (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param))) := by
  let A := eqn value (numeral 1)
  obtain ⟨h⟩ := outputTransport (OriginalDecodedExchangeEquation.exchange n arity) value (numeral 1)
    ![child,param] (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩) (withHyp hv A)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem valueBackward (child param value : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) value child param))) :
    Nonempty (Derivation body Delta ((graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param).imp
      (eqn value (numeral 1)))) := by
  let A := graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param
  obtain ⟨h⟩ := valueUnique (OriginalDecodedExchangeEquation.exchange n arity) value (numeral 1)
    ![child,param] (withHyp hv A) (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction h⟩

theorem orderedFour (param qr qb ar ab deps d1 d2 d3 v0 v1 v2 v3 vals t1 t2 t3 : OTerm alpha)
    (d0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode deps qr d1)))
    (d1h : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d1 qb d2)))
    (d2h : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d2 ar d3)))
    (d3h : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode d3 ab z)))
    (a0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode vals v0 t1)))
    (a1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t1 v1 t2)))
    (a2 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t2 v2 t3)))
    (a3 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode t3 v3 z)))
    (h0 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v0 qr param)))
    (h1 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v1 qb param)))
    (h2 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v2 ar param)))
    (h3 : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) v3 ab param)))
    : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.answerMap n arity) vals deps param)) := by
  have hnil := OriginalDecodedExchangeEquation.StepProof.nilValue n arity (body := body) (Delta := Delta) param
  have ht3 := OriginalDecodedExchangeEquation.StepProof.consValue n arity d3 ab z param v3 z t3 d3h h3 hnil a3
  have ht2 := OriginalDecodedExchangeEquation.StepProof.consValue n arity d2 ar d3 param v2 t3 t2 d2h h2 ht3 a2
  have ht1 := OriginalDecodedExchangeEquation.StepProof.consValue n arity d1 qb d2 param v1 t2 t1 d1h h1 ht2 a1
  exact OriginalDecodedExchangeEquation.StepProof.consValue n arity deps qr d1 param v0 t1 vals d0 h0 ht1 a0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.ValuesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedBinaryRecurrence.ValuesProof
