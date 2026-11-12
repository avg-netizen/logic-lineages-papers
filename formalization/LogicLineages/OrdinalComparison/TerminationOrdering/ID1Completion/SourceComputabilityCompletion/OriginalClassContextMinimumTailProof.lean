module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalClassContextMinimumTail OriginalClassContextMinimumTailWiringProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem transferKey (R : Program 2) (seed out parameter erasedSeed erasedOut tailParameter key : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (rightOf OriginalClassContextObserver.erasedObject) erasedSeed seed parameter)))
    (hsp : Nonempty (Derivation body Delta (graph2 OriginalClassContextObserver.parentParameter tailParameter seed parameter)))
    (ho : Nonempty (Derivation body Delta (graph2 (rightOf OriginalClassContextObserver.erasedObject) erasedOut out parameter)))
    (hop : Nonempty (Derivation body Delta (graph2 OriginalClassContextObserver.parentParameter tailParameter out parameter)))
    (he : Nonempty (Derivation body Delta
      ((graph2 (OriginalClassContextObserver.erasedKey R) key seed parameter).iff
        (graph2 (OriginalClassContextObserver.erasedKey R) key out parameter)))) :
    Nonempty (Derivation body Delta
      ((graph2 R key erasedSeed tailParameter).iff (graph2 R key erasedOut tailParameter))) := by
  let A := graph2 R key erasedSeed tailParameter
  let B := graph2 R key erasedOut tailParameter
  have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hks⟩ := keyForward R seed parameter erasedSeed tailParameter key (withHyp hs A) (withHyp hsp A) hA
  obtain ⟨hf⟩ := withHyp (andLeft he) A
  obtain ⟨hout⟩ := keyBackward R out parameter erasedOut tailParameter key
    (withHyp ho A) (withHyp hop A) ⟨Derivation.implicationElimination hf hks⟩
  have hB : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hko⟩ := keyForward R out parameter erasedOut tailParameter key (withHyp ho B) (withHyp hop B) hB
  obtain ⟨hb⟩ := withHyp (andRight he) B
  obtain ⟨hin⟩ := keyBackward R seed parameter erasedSeed tailParameter key
    (withHyp hs B) (withHyp hsp B) ⟨Derivation.implicationElimination hb hko⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hout)
    (Derivation.implicationIntroduction hin)⟩

theorem transferRank (seed out parameter erasedSeed erasedOut rank : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 (rightOf OriginalClassContextObserver.erasedObject) erasedSeed seed parameter)))
    (ho : Nonempty (Derivation body Delta (graph2 (rightOf OriginalClassContextObserver.erasedObject) erasedOut out parameter)))
    (he : Nonempty (Derivation body Delta
      ((graph2 OriginalClassContextObserver.erasedRank rank seed parameter).iff
        (graph2 OriginalClassContextObserver.erasedRank rank out parameter)))) :
    Nonempty (Derivation body Delta
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedSeed).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedOut))) := by
  let A := graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedSeed
  let B := graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedOut
  have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hks⟩ := rankForward seed parameter erasedSeed rank (withHyp hs A) hA
  obtain ⟨hf⟩ := withHyp (andLeft he) A
  obtain ⟨hout⟩ := rankBackward out parameter erasedOut rank (withHyp ho A) ⟨Derivation.implicationElimination hf hks⟩
  have hB : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hko⟩ := rankForward out parameter erasedOut rank (withHyp ho B) hB
  obtain ⟨hb⟩ := withHyp (andRight he) B
  obtain ⟨hin⟩ := rankBackward seed parameter erasedSeed rank (withHyp hs B) ⟨Derivation.implicationElimination hb hko⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hout)
    (Derivation.implicationIntroduction hin)⟩

theorem actualObservedMinimumTailKeyRank :
    OriginalClassContextMinimumTailTargets.ActualObservedMinimumTailKeyRank := by
  intro p H G W P body alpha Delta seed out parameter context extended d gamma tailParameter
    seedObject outObject erasedSeedObject erasedOutObject erasedSeed erasedOut key rank
  let A := Premises p H G W P seed out parameter context extended d gamma tailParameter
    seedObject outObject erasedSeedObject erasedOutObject erasedSeed erasedOut
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hd := andLeft h
  have h1 := andRight h
  have hp := andLeft h1
  have h2 := andRight h1
  have hc := andLeft h2
  have h3 := andRight h2
  have hr := andLeft h3
  have h4 := andRight h3
  have hso := andLeft h4
  have h5 := andRight h4
  have hoo := andLeft h5
  have h6 := andRight h5
  have hse := andLeft h6
  have h7 := andRight h6
  have hoe := andLeft h7
  have h8 := andRight h7
  have hsparts := andLeft h8
  have h9 := andRight h8
  have hoparts := andLeft h9
  have htail := andRight h9
  have hs := wires seed parameter context extended gamma tailParameter seedObject erasedSeedObject erasedSeed
    hp hso hse hsparts htail
  have ho := wires out parameter context extended gamma tailParameter outObject erasedOutObject erasedOut
    hp hoo hoe hoparts htail
  have he := OriginalClassContextMinimumTailConsProof.outputCons p H G W P
    seed out parameter context extended d gamma key rank hd hp hc hr
  obtain ⟨hresult⟩ := andIntro
    (transferKey p.base.oldRepresentative seed out parameter erasedSeed erasedOut tailParameter key
      (andLeft hs) (andRight hs) (andLeft ho) (andRight ho) (andLeft he))
    (transferRank seed out parameter erasedSeed erasedOut rank (andLeft hs) (andLeft ho) (andRight he))
  exact ⟨Derivation.implicationIntroduction hresult⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextMinimumTailProof.actualObservedMinimumTailKeyRank
