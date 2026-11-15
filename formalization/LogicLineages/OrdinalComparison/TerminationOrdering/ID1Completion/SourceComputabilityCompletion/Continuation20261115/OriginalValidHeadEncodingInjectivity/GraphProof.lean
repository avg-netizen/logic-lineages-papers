module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.ArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadEncodingBridge.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.GraphProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm trans congSuc addZero addSucc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 OriginalHeadEncodingBridge ArithmeticProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem leftValue (P : Program 1) (out raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 P out raw))) :
    Nonempty (Derivation body Delta (graph1 (sumLeft P) (even out) raw)) :=
  binaryValue InternalArithmeticPrograms.addition P P (even out) out out ![raw]
    (InternalArithmeticProgramsSupportProof.additionValue out out) h h

theorem rightValue (P : Program 1) (out raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 P out raw))) :
    Nonempty (Derivation body Delta (graph1 (sumRight P) (odd out) raw)) :=
  unaryValue .succ (sumLeft P) (odd out) (even out) ![raw]
    (successorValue (Fin.cons (even out) Fin.elim0)) (leftValue P out raw h)

theorem branchValue (i : Fin 6) (raw : OTerm alpha) :
    Nonempty (Derivation body Delta (graph1 (branchCode i.val) (code i raw) raw)) := by
  have hp : Nonempty (Derivation body Delta (graph1 (.projection 0) raw raw)) := projectionValue 0 ![raw]
  fin_cases i
  · exact outputTransport (OriginalRawSyntaxTransport.constant 1 0) z (even z) ![raw]
      ⟨symm (addZero z)⟩ (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 ![raw])
  · exact outputTransport (OriginalRawSyntaxTransport.constant 1 2) (suc (suc z)) (even (suc z)) ![raw]
      ⟨symm (trans (addSucc (suc z) z) (congSuc (addZero (suc z))))⟩
      (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 2 ![raw])
  · exact rightValue _ _ raw (leftValue _ _ raw hp)
  · exact rightValue _ _ raw (rightValue _ _ raw (leftValue _ _ raw hp))
  · exact rightValue _ _ raw (rightValue _ _ raw (rightValue _ _ raw (leftValue _ _ raw hp)))
  · exact rightValue _ _ raw (rightValue _ _ raw (rightValue _ _ raw (rightValue _ _ raw hp)))

theorem outputCode (i : Fin 6) (raw payload out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral i.val) payload)))
    (he : Nonempty (Derivation body Delta (graph1 encodeHead out raw))) :
    Nonempty (Derivation body Delta (eqn out (code i payload))) :=
  valueUnique (branchCode i.val) out (code i payload) ![payload]
    ((OriginalHeadEncodingBridge.InternalProof.internalTagFactor body alpha Delta i raw payload out hp).mp he)
    (branchValue i payload)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.GraphProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.GraphProof
