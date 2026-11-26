module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankMemoOpeningProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (suc z eqn)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawVariableRankLeafProof OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransport
open RankMemoDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A conditional zero branch, not an assertion that admitted full E-code zero
occurs. Actual variable constructor rank agrees with the total fallback. -/
theorem variableZero (packed typ raw index rank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw index)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed))) :
 Nonempty (Derivation body Delta (graph1 decoder rank z)) := by
 have he := rankVariableForward raw rank index hc (rankPackedForward packed rank typ raw hp hr)
 obtain ⟨he⟩ := he
 exact outputTransport decoder (numeral 1) rank (Fin.cons z Fin.elim0) ⟨symm he⟩
   (RankMemoRecurrenceProof.actualZero body alpha Delta)

theorem variableSuccessor (stage tab packed typ raw field rank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hc : Nonempty (Derivation body Delta (graph1 variableConstructor raw field)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hg : Nonempty (Derivation body Delta (graph2 tag (numeral 0) stage tab))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 have he := rankVariableForward raw rank field hc (rankPackedForward packed rank typ raw hp hr)
 have hv := RankMemoDispatchProof.dispatch0 stage tab (numeral 1) hg
   (constantValue 1 (![stage,tab] : Fin 2 → OTerm alpha))
 obtain ⟨he⟩ := he
 exact outputTransport decoder (numeral 1) rank (Fin.cons (suc stage) Fin.elim0) ⟨symm he⟩
   (RankMemoSuccessorProof.atSuccessor stage tab (numeral 1) ht hv)

theorem bottomSuccessor (stage tab packed typ raw field rank : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hc : Nonempty (Derivation body Delta (graph1 bottomConstructor raw field)))
 (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank packed)))
 (ht : Nonempty (Derivation body Delta (graph1 table tab stage)))
 (hg : Nonempty (Derivation body Delta (graph2 tag (numeral 3) stage tab))) :
 Nonempty (Derivation body Delta (graph1 decoder rank (suc stage))) := by
 have he := rankBottomForward raw rank field hc (rankPackedForward packed rank typ raw hp hr)
 have hv := RankMemoDispatchProof.dispatch3 stage tab (numeral 0) hg
   (constantValue 0 (![stage,tab] : Fin 2 → OTerm alpha))
 obtain ⟨he⟩ := he
 exact outputTransport decoder (numeral 0) rank (Fin.cons (suc stage) Fin.elim0) ⟨symm he⟩
   (RankMemoSuccessorProof.atSuccessor stage tab (numeral 0) ht hv)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLeafProof
