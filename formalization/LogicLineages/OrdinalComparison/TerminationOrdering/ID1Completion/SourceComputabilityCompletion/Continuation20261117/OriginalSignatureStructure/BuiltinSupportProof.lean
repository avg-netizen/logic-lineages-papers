module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalConcreteSignatureEquations.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open Continuation20261116.OriginalConcreteHeadSignature
open Continuation20261115.OriginalHeadDecoderValidity.SupportProof
open Continuation20261114
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem arrowValue (p q : Program 1) (raw a b packed : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 p a raw)))
    (hq : Nonempty (Derivation body Delta (graph1 q b raw)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed a b))) :
    Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.arrow p q) (suc packed) raw)) :=
  unaryValue .succ (.composition InternalPairing.pairing ![p,q]) (suc packed) packed ![raw]
    (successorValue (Fin.cons packed Fin.elim0))
    (binaryValue InternalPairing.pairing p q packed a b ![raw] hk hp hq)

theorem finish (n : Nat) (arity : Fin n → Nat) (tag : Fin 4) (raw payload result packed out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) payload)))
    (hr : Nonempty (Derivation body Delta (graph1 (OriginalHeadResult.branchResult tag.val) result payload)))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed result z))) :
    Nonempty (Derivation body Delta (graph1 (signature n arity) out raw)) ↔
    Nonempty (Derivation body Delta (eqn out (suc packed))) := by
  let tag6 : Fin 6 := ⟨tag.val,Nat.lt_trans tag.isLt (by decide)⟩
  have hr' := (OriginalHeadResult.InternalProof.internalTagFactor body alpha Delta tag6 raw payload result hp).mpr hr
  have ha : Nonempty (Derivation body Delta (graph1 (arguments n arity) z raw)) := by
    apply (OriginalConcreteHeadArguments.TagProof.internalTagFactor n arity body alpha Delta tag6 raw payload z hp).mpr
    have h : branchArguments n arity tag.val = constant 1 0 := by fin_cases tag <;> rfl
    change Nonempty (Derivation body Delta (graph1 (branchArguments n arity tag.val) z payload))
    rw [h]
    exact constantValue 0 ![payload]
  exact OriginalConcreteSignatureEquations.Proof.outputEquation n arity raw packed out
    (OriginalConcreteSignatureEquations.SupportProof.successValue n arity raw result z packed hr' ha hk hg)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.BuiltinSupportProof
