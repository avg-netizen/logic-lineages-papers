module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalInterfacesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParametersQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal OriginalRawVariableRank
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rankFromFold (out d k raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph3 (fold .rank) out d k raw))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) := by
  obtain ⟨hi⟩ := (OriginalRawSyntaxTransportInternalInterfacesProof.actualRawSyntaxInternalInterfaces
    body alpha Delta out d k raw).2.2
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hi) h⟩

theorem rankToFold (out d k raw : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (graph3 (fold .rank) out d k raw)) := by
  obtain ⟨hi⟩ := (OriginalRawSyntaxTransportInternalInterfacesProof.actualRawSyntaxInternalInterfaces
    body alpha Delta out d k raw).2.2
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hi) h⟩

theorem rankSumForward (out first second firstRank secondRank : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 variableRankRaw firstRank first)))
    (hs : Nonempty (Derivation body Delta (graph1 variableRankRaw secondRank second)))
    (ho : Nonempty (Derivation body Delta (graph2 rankSum out first second))) :
    Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition out firstRank secondRank)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons first (Fin.cons second Fin.elim0)
  exact binaryRecover InternalArithmeticPrograms.addition
    (.composition variableRankRaw (fun _ : Fin 1 => .projection 0))
    (.composition variableRankRaw (fun _ : Fin 1 => .projection 1))
    out firstRank secondRank xs ho
    (unaryValue variableRankRaw (.projection 0) firstRank first xs hf (projectionValue 0 xs))
    (unaryValue variableRankRaw (.projection 1) secondRank second xs hs (projectionValue 1 xs))

theorem rankSumBackward (out first second firstRank secondRank : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph1 variableRankRaw firstRank first)))
    (hs : Nonempty (Derivation body Delta (graph1 variableRankRaw secondRank second)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition out firstRank secondRank))) :
    Nonempty (Derivation body Delta (graph2 rankSum out first second)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons first (Fin.cons second Fin.elim0)
  exact binaryValue InternalArithmeticPrograms.addition
    (.composition variableRankRaw (fun _ : Fin 1 => .projection 0))
    (.composition variableRankRaw (fun _ : Fin 1 => .projection 1))
    out firstRank secondRank xs ho
    (unaryValue variableRankRaw (.projection 0) firstRank first xs hf (projectionValue 0 xs))
    (unaryValue variableRankRaw (.projection 1) secondRank second xs hs (projectionValue 1 xs))

theorem rankPackedForward (packed out tau raw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw out packed))) :
    Nonempty (Derivation body Delta (graph1 variableRankRaw out raw)) :=
  unaryRecover variableRankRaw InternalUnpair.right out raw (Fin.cons packed Fin.elim0)
    ho (pairRight packed tau raw hp)

theorem rankPackedBackward (packed out tau raw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed tau raw)))
    (ho : Nonempty (Derivation body Delta (graph1 variableRankRaw out raw))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw out packed)) :=
  unaryValue variableRankRaw InternalUnpair.right out raw (Fin.cons packed Fin.elim0)
    ho (pairRight packed tau raw hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankSupportProof
