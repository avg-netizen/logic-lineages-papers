module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedSuccessShape.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ActiveDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm trans)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261115 Induction
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

theorem preserved (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types st tt : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag st left)))
    (hr : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag tt right)))
    (hmatch : Nonempty (Derivation body Delta (eqn st tt)))
    (hactive : Nonempty (Derivation body Delta (OriginalDecodedSuccessShape.Targets.active st)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  apply OriginalTypedDecoderInternalBranchProof.orCases hactive
  · have ht : Nonempty (Derivation body ((eqn st (numeral 1)) :: Delta) (eqn st (numeral 1))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hlt,hrt⟩ := tagValues 1 left right st tt (withHyp hl _) (withHyp hr _) (withHyp hmatch _) ht
    exact ModeDispatchProof.tag1 n arity arguments left right node window typ gamma context symbols types hlt hrt
      (withHyp henv _) (withHyp hedge _) (withHyp ih _) (withHyp ha _) (withHyp hp _)
  · skip
    have htail1 : Nonempty (Derivation body (((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply OriginalTypedDecoderInternalBranchProof.orCases htail1
    · have ht : Nonempty (Derivation body ((eqn st (numeral 2)) :: ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 2))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      obtain ⟨hlt,hrt⟩ := tagValues 2 left right st tt (withHyp (withHyp hl _) _) (withHyp (withHyp hr _) _) (withHyp (withHyp hmatch _) _) ht
      exact ModeDispatchProof.tag2 n arity arguments left right node window typ gamma context symbols types hlt hrt
        (withHyp (withHyp henv _) _) (withHyp (withHyp hedge _) _) (withHyp (withHyp ih _) _) (withHyp (withHyp ha _) _) (withHyp (withHyp hp _) _)
    · skip
      have htail2 : Nonempty (Derivation body (((eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      apply OriginalTypedDecoderInternalBranchProof.orCases htail2
      · have ht : Nonempty (Derivation body ((eqn st (numeral 4)) :: ((eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 4))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        obtain ⟨hlt,hrt⟩ := tagValues 4 left right st tt (withHyp (withHyp (withHyp hl _) _) _) (withHyp (withHyp (withHyp hr _) _) _) (withHyp (withHyp (withHyp hmatch _) _) _) ht
        exact ModeDispatchProof.tag4 n arity arguments left right node window typ gamma context symbols types hlt hrt
          (withHyp (withHyp (withHyp henv _) _) _) (withHyp (withHyp (withHyp hedge _) _) _) (withHyp (withHyp (withHyp ih _) _) _) (withHyp (withHyp (withHyp ha _) _) _) (withHyp (withHyp (withHyp hp _) _) _)
      · skip
        have htail3 : Nonempty (Derivation body (((eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: ((eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 5) ⊔ eqn st (numeral 7))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
        apply OriginalTypedDecoderInternalBranchProof.orCases htail3
        · have ht : Nonempty (Derivation body ((eqn st (numeral 5)) :: ((eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: ((eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 5))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          obtain ⟨hlt,hrt⟩ := tagValues 5 left right st tt (withHyp (withHyp (withHyp (withHyp hl _) _) _) _) (withHyp (withHyp (withHyp (withHyp hr _) _) _) _) (withHyp (withHyp (withHyp (withHyp hmatch _) _) _) _) ht
          exact ModeDispatchProof.tag5 n arity arguments left right node window typ gamma context symbols types hlt hrt
            (withHyp (withHyp (withHyp (withHyp henv _) _) _) _) (withHyp (withHyp (withHyp (withHyp hedge _) _) _) _) (withHyp (withHyp (withHyp (withHyp ih _) _) _) _) (withHyp (withHyp (withHyp (withHyp ha _) _) _) _) (withHyp (withHyp (withHyp (withHyp hp _) _) _) _)
        · skip
          have ht : Nonempty (Derivation body ((eqn st (numeral 7)) :: ((eqn st (numeral 5) ⊔ eqn st (numeral 7))) :: ((eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7)))) :: ((eqn st (numeral 2) ⊔ (eqn st (numeral 4) ⊔ (eqn st (numeral 5) ⊔ eqn st (numeral 7))))) :: Delta) (eqn st (numeral 7))) := ⟨Derivation.hypothesis List.mem_cons_self⟩
          obtain ⟨hlt,hrt⟩ := tagValues 7 left right st tt (withHyp (withHyp (withHyp (withHyp hl _) _) _) _) (withHyp (withHyp (withHyp (withHyp hr _) _) _) _) (withHyp (withHyp (withHyp (withHyp hmatch _) _) _) _) ht
          exact ModeDispatchProof.tag7 n arity arguments left right node window typ gamma context symbols types hlt hrt
            (withHyp (withHyp (withHyp (withHyp henv _) _) _) _) (withHyp (withHyp (withHyp (withHyp hedge _) _) _) _) (withHyp (withHyp (withHyp (withHyp ih _) _) _) _) (withHyp (withHyp (withHyp (withHyp ha _) _) _) _) (withHyp (withHyp (withHyp (withHyp hp _) _) _) _)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ActiveDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ActiveDispatchProof
