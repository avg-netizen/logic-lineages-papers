module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.SumProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.LeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.CasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalValidHeadEncodingInjectivity.GraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.TaggedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn z suc)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalValidHeadEncodingInjectivity.ArithmeticProof (code)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem branchTag (n : Nat) (i : Fin 6) (tag payload : OTerm alpha)
    (h : Nonempty (Derivation body Delta (CasesProof.branch n i tag payload))) :
    Nonempty (Derivation body Delta (eqn tag (numeral i.val))) := by
  unfold CasesProof.branch at h
  split_ifs at h with hi hr
  · exact andLeft h
  · exact andLeft h
  · exact h

theorem taggedValue (n : Nat) (i : Fin 6) (raw payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral i.val) payload)))
    (hb : Nonempty (Derivation body Delta (CasesProof.branch n i (numeral i.val) payload))) :
    Nonempty (Derivation body Delta (graph1 (convert n) raw (code i payload))) := by
  fin_cases i
  · have hz : Nonempty (Derivation body Delta (eqn payload z)) := andRight hb
    have hp0 := InternalApplicationValidityStackAppendRunProof.rightTransport
      InternalPairing.pairing raw z payload z hz hp
    exact SumProof.leftValue _ _ z raw (LeafProof.booleanZero raw hp0)
  · have hz : Nonempty (Derivation body Delta (eqn payload z)) := andRight hb
    have hp0 := InternalApplicationValidityStackAppendRunProof.rightTransport
      InternalPairing.pairing raw (suc z) payload z hz hp
    exact SumProof.leftValue _ _ (suc z) raw (LeafProof.booleanOne raw hp0)
  · exact SumProof.rightValue _ _ _ raw
      (SumProof.leftValue _ _ payload raw (LeafProof.payloadValue 2 payload raw hp))
  · exact SumProof.rightValue _ _ _ raw
      (SumProof.rightValue _ _ _ raw
        (SumProof.leftValue _ _ payload raw (LeafProof.payloadValue 3 payload raw hp)))
  · exact SumProof.rightValue _ _ _ raw
      (SumProof.rightValue _ _ _ raw
        (SumProof.rightValue _ _ _ raw
          (SumProof.leftValue _ _ payload raw (LeafProof.payloadValue 4 payload raw hp))))
  · have hn : Nonempty (Derivation body Delta (InternalLessThan.strictLess payload (numeral n))) := andRight hb
    exact SumProof.rightValue _ _ _ raw
      (SumProof.rightValue _ _ _ raw
        (SumProof.rightValue _ _ _ raw
          (SumProof.rightValue _ _ payload raw (LeafProof.rankedValue n payload raw hp hn))))

theorem atBranch (n : Nat) (i : Fin 6) (raw tag payload encoded : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)))
    (hb : Nonempty (Derivation body Delta (CasesProof.branch n i tag payload)))
    (he : Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadEncodingBridge.encodeHead encoded raw))) :
    Nonempty (Derivation body Delta (graph1 (convert n) raw encoded)) := by
  have ht := branchTag n i tag payload hb
  have hp' := headTransport InternalPairing.pairing raw tag (numeral i.val) (Fin.cons payload Fin.elim0) ht hp
  have hb' : Nonempty (Derivation body Delta (CasesProof.branch n i (numeral i.val) payload)) := by
    unfold CasesProof.branch at hb ⊢
    split_ifs at hb ⊢ with hi hr
    · exact InternalApplicationStepPeelSupportProof.andIntro ⟨InternalTagArithmeticSupportProof.refl _⟩ (andRight hb)
    · exact InternalApplicationStepPeelSupportProof.andIntro ⟨InternalTagArithmeticSupportProof.refl _⟩ (andRight hb)
    · exact ⟨InternalTagArithmeticSupportProof.refl _⟩
  obtain ⟨hc⟩ := OriginalValidHeadEncodingInjectivity.GraphProof.outputCode i raw payload encoded hp' he
  exact headTransport (convert n) raw (code i payload) encoded Fin.elim0 ⟨symm hc⟩
    (taggedValue n i raw payload hp' hb')
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.TaggedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedHeadConversion.TaggedProof
