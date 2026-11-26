module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ActiveDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (trans symm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open ExchangeInduction Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem tagValues (tag : Nat) (left right st tt : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag st left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag tt right)))
    (hmatch : Nonempty (Derivation body Delta (eqn st tt)))
    (ht : Nonempty (Derivation body Delta (eqn st (numeral tag)))) :
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral tag) left)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral tag) right)) := by
  obtain ⟨hm⟩ := hmatch
  obtain ⟨ht'⟩ := ht
  exact ⟨outputTransport OriginalRawSyntaxTransport.rawTag st (numeral tag) ![left] ⟨ht'⟩ hl,
    outputTransport OriginalRawSyntaxTransport.rawTag tt (numeral tag) ![right] ⟨trans (symm hm) ht'⟩ hr⟩
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right node window lv rv st tt : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag st left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag tt right)))
    (hmatch : Nonempty (Derivation body Delta (eqn st tt)))
    (ha : Nonempty (Derivation body Delta (OriginalDecodedSuccessShape.Targets.active st)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases ha
  · have ht : Nonempty (Derivation body (eqn st (numeral 1) :: Delta) (eqn st (numeral 1))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hlt,hrt⟩ := tagValues 1 left right st tt (withHyp hl _) (withHyp hr _) (withHyp hmatch _) ht
    exact TaggedLambdaProof.preserved n arity left right node window lv rv hlt hrt
      (withHyp hp _) (withHyp he _) (withHyp hlv _) (withHyp hrv _) (withHyp ih _)
  · skip
    have htail1 : Nonempty (Derivation body ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply OriginalTypedDecoderInternalBranchProof.orCases htail1
    · have ht : Nonempty (Derivation body (eqn st (numeral 2) :: (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 2))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hlt,hrt⟩ := tagValues 2 left right st tt (withHyp (withHyp hl _) _) (withHyp (withHyp hr _) _) (withHyp (withHyp hmatch _) _) ht
      exact TaggedApplicationProof.preserved n arity left right node window lv rv hlt hrt
        (withHyp (withHyp hp _) _) (withHyp (withHyp he _) _) (withHyp (withHyp hlv _) _) (withHyp (withHyp hrv _) _) (withHyp (withHyp ih _) _)
    · skip
      have htail2 : Nonempty (Derivation body ((eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply OriginalTypedDecoderInternalBranchProof.orCases htail2
      · have ht : Nonempty (Derivation body (eqn st (numeral 4) :: (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 4))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        obtain ⟨hlt,hrt⟩ := tagValues 4 left right st tt (withHyp (withHyp (withHyp hl _) _) _) (withHyp (withHyp (withHyp hr _) _) _) (withHyp (withHyp (withHyp hmatch _) _) _) ht
        exact TaggedOrdinaryProof.preserved n arity left right node window lv rv hlt hrt
          (withHyp (withHyp (withHyp hp _) _) _) (withHyp (withHyp (withHyp he _) _) _) (withHyp (withHyp (withHyp hlv _) _) _) (withHyp (withHyp (withHyp hrv _) _) _) (withHyp (withHyp (withHyp ih _) _) _)
      · skip
        have htail3 : Nonempty (Derivation body ((eqn st (numeral 5) ⊔ eqn st (numeral 7)) :: (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 5) ⊔ eqn st (numeral 7))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply OriginalTypedDecoderInternalBranchProof.orCases htail3
        · have ht : Nonempty (Derivation body (eqn st (numeral 5) :: (eqn st (numeral 5) ⊔ eqn st (numeral 7)) :: (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 5))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          obtain ⟨hlt,hrt⟩ := tagValues 5 left right st tt (withHyp (withHyp (withHyp (withHyp hl _) _) _) _) (withHyp (withHyp (withHyp (withHyp hr _) _) _) _) (withHyp (withHyp (withHyp (withHyp hmatch _) _) _) _) ht
          exact TaggedNumberedProof.preserved n arity left right node window lv rv hlt hrt
            (withHyp (withHyp (withHyp (withHyp hp _) _) _) _) (withHyp (withHyp (withHyp (withHyp he _) _) _) _) (withHyp (withHyp (withHyp (withHyp hlv _) _) _) _) (withHyp (withHyp (withHyp (withHyp hrv _) _) _) _) (withHyp (withHyp (withHyp (withHyp ih _) _) _) _)
        · skip
          have ht : Nonempty (Derivation body (eqn st (numeral 7) :: (eqn st (numeral 5) ⊔ eqn st (numeral 7)) :: (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: Delta) (eqn st (numeral 7))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          obtain ⟨hlt,hrt⟩ := tagValues 7 left right st tt (withHyp (withHyp (withHyp (withHyp hl _) _) _) _) (withHyp (withHyp (withHyp (withHyp hr _) _) _) _) (withHyp (withHyp (withHyp (withHyp hmatch _) _) _) _) ht
          exact TaggedConsProof.preserved n arity left right node window lv rv hlt hrt
            (withHyp (withHyp (withHyp (withHyp hp _) _) _) _) (withHyp (withHyp (withHyp (withHyp he _) _) _) _) (withHyp (withHyp (withHyp (withHyp hlv _) _) _) _) (withHyp (withHyp (withHyp (withHyp hrv _) _) _) _) (withHyp (withHyp (withHyp (withHyp ih _) _) _) _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ActiveDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ActiveDispatchProof
