module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.FieldProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
/-- The literal eight original decoder cases, with each active child checked at
its OWN original cutoff child+1 and bound child. Unknown tags are excluded.
No parent-table lookup or assumed child validity is hidden in this formula. -/
def allowed {alpha : Type} (n : Nat) (tagValue payloadValue first second head : OTerm alpha) : Formula alpha :=
  (eqn tagValue (numeral 0) ⊔ eqn tagValue (numeral 3)) ⊔
  ((eqn tagValue (numeral 1) ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first) ⊔
  (((eqn tagValue (numeral 2) ⊔ eqn tagValue (numeral 7)) ⊓
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first ⊓
       graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)) ⊔
  ((eqn tagValue (numeral 4) ⊓
      (graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
       graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first)) ⊔
  ((eqn tagValue (numeral 5) ⊓
      ((graph1 (OriginalHeadDecoderValidity.check n) (numeral 1) head ⊓
        graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first) ⊓
        graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)) ⊔
    (eqn tagValue (numeral 6) ⊓ eqn payloadValue (numeral 0))))))
/-- Original recursive guard constructor characterization on every raw code.
Only actual total field observations are premises. Child descent, all table
witnesses, sufficient-fuel/bound obligations and cross-bound transport are paid
internally. This is not a decoded-node dependency supplier or installation claim. -/
def InternalGuardConstructors : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (rawCode tagValue payloadValue first second head : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawCode tagValue payloadValue)) →
  Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first rawCode)) →
  Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second rawCode)) →
  Nonempty (Derivation body Delta
    (graph1 (OriginalCodeValidityGuard.FieldProof.headOf (.projection 0)) head rawCode)) →
  (Nonempty (Derivation body Delta
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) rawCode)) ↔
    Nonempty (Derivation body Delta (allowed n tagValue payloadValue first second head)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityConstructors.Targets
