module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairImageProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairRecursionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalRawListRecursionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nilValue (param : OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 pairRoots z z param)) :=
  InternalRawListRecursionProof.nilValue (OriginalRawSyntaxTransport.constant 1 0) pairStep
    z ![param] (InternalAcceptanceConjunctionProof.constantZeroValue ![param])

theorem stepValue (head rest param mappedHead out : OTerm alpha)
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mappedHead param head)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest))) :
    Nonempty (Derivation body Delta (programGraph pairStep out ![head,rest,param])) := by
  apply binaryValue InternalListCodec.consCode
    (InternalApplicationCertificateConstructors.pairOf (.projection 2) (.projection 0))
    (.projection 1) out mappedHead rest ![head,rest,param] ho
  · exact binaryValue InternalPairing.pairing (.projection 2) (.projection 0)
      mappedHead param head ![head,rest,param] hh (projectionValue 2 ![head,rest,param]) (projectionValue 0 ![head,rest,param])
  · exact projectionValue 1 ![head,rest,param]

theorem consBackward (raw head tail param mappedHead rest out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mappedHead param head)))
    (ht : Nonempty (Derivation body Delta (graph2 pairRoots rest tail param)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest))) :
    Nonempty (Derivation body Delta (graph2 pairRoots out raw param)) :=
  InternalRawListRecursionProof.consValue (OriginalRawSyntaxTransport.constant 1 0) pairStep
    raw head tail rest out ![param] hc ht (stepValue head rest param mappedHead out hh ho)

theorem consForward (raw head tail param mappedHead rest out : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hh : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing mappedHead param head)))
    (ht : Nonempty (Derivation body Delta (graph2 pairRoots rest tail param)))
    (hv : Nonempty (Derivation body Delta (graph2 pairRoots out raw param))) :
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out mappedHead rest)) := by
  apply programCases InternalListCodec.consCode ![mappedHead,rest] _
  intro beta j Theta value hj ho
  have hx : (fun i => (![mappedHead,rest] i).relabel j) = (![mappedHead.relabel j,rest.relabel j] : Fin 2 → OTerm beta) := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at ho
  simp only [graph2Rename]
  have hc' := renameInto hc j Theta hj
  have hh' := renameInto hh j Theta hj
  have ht' := renameInto ht j Theta hj
  have hv' := renameInto hv j Theta hj
  simp only [graph2Rename] at hc' hh' ht' hv'
  have he := consBackward (raw.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j)
    (mappedHead.relabel j) (rest.relabel j) value hc' hh' ht' ho
  exact outputTransport InternalListCodec.consCode value (out.relabel j)
    ![mappedHead.relabel j,rest.relabel j]
    (valueUnique pairRoots value (out.relabel j) ![raw.relabel j,param.relabel j] he hv') ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairRecursionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.PairRecursionProof
