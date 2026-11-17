module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ActiveDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof FactsProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm trans)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
theorem tagValues (tag : Nat) (left right st tt : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag st left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag tt right)))
    (hm : Nonempty (Derivation body Delta (eqn st tt)))
    (ht : Nonempty (Derivation body Delta (eqn st (numeral tag)))) :
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral tag) left)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral tag) right)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨ht⟩ := ht
  exact ⟨outputTransport _ st (numeral tag) ![left] ⟨ht⟩ hl,
    outputTransport _ tt (numeral tag) ![right] ⟨trans (symm hm) ht⟩ hr⟩
theorem reversed (n : Nat) (arity : Fin n → Nat)
    (left right node rev window symbols types st tt : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag st left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag tt right)))
    (hm : Nonempty (Derivation body Delta (eqn st tt)))
    (ha : Nonempty (Derivation body Delta (OriginalDecodedSuccessShape.Targets.active st)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply orCases ha
  · intro Theta0 hi0 ht
    obtain ⟨hlt,hrt⟩ := tagValues 1 left right st tt (weakenProof hl hi0) (weakenProof hr hi0) (weakenProof hm hi0) ht
    exact TaggedLambdaProof.reversed n arity left right node rev window symbols types hlt hrt (h.weaken Theta0 hi0) (weakenProof ih hi0)
  · intro Theta0 hi0 ht
    apply orCases ht
    · intro Theta1 hi1 ht
      obtain ⟨hlt,hrt⟩ := tagValues 2 left right st tt (weakenProof hl (fun p hp => hi1 p (hi0 p hp))) (weakenProof hr (fun p hp => hi1 p (hi0 p hp))) (weakenProof hm (fun p hp => hi1 p (hi0 p hp))) ht
      exact TaggedApplicationProof.reversed n arity left right node rev window symbols types hlt hrt (h.weaken Theta1 (fun p hp => hi1 p (hi0 p hp))) (weakenProof ih (fun p hp => hi1 p (hi0 p hp)))
    · intro Theta1 hi1 ht
      apply orCases ht
      · intro Theta2 hi2 ht
        obtain ⟨hlt,hrt⟩ := tagValues 4 left right st tt (weakenProof hl (fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp))) (weakenProof hr (fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp))) (weakenProof hm (fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp))) ht
        exact TaggedOrdinaryProof.reversed n arity left right node rev window symbols types hlt hrt (h.weaken Theta2 (fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp))) (weakenProof ih (fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)))
      · intro Theta2 hi2 ht
        apply orCases ht
        · intro Theta3 hi3 ht
          obtain ⟨hlt,hrt⟩ := tagValues 5 left right st tt (weakenProof hl (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) (weakenProof hr (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) (weakenProof hm (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) ht
          exact TaggedNumberedProof.reversed n arity left right node rev window symbols types hlt hrt (h.weaken Theta3 (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) (weakenProof ih (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp)))
        · intro Theta3 hi3 ht
          obtain ⟨hlt,hrt⟩ := tagValues 7 left right st tt (weakenProof hl (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) (weakenProof hr (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) (weakenProof hm (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) ht
          exact TaggedConsProof.reversed n arity left right node rev window symbols types hlt hrt (h.weaken Theta3 (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp))) (weakenProof ih (fun p hp => hi3 p ((fun p hp => hi2 p ((fun p hp => hi1 p (hi0 p hp)) p hp)) p hp)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ActiveDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.ActiveDispatchProof
