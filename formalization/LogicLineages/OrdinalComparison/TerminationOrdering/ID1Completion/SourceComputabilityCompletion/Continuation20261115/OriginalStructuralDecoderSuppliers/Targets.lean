module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- Original InstalledExchangeRecursor validity on all vectors, including failures. -/
def NativeValid : Prop := ∀ (n : Nat) (v : List.Vector Nat 3),
  evaluate (valid n) v = InstalledExchangeRecursor.validValue n v
/-- Original encoded Context window projection, including default0 on rejection. -/
def NativeWindow : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (window n) v = InstalledExchangeRecursor.windowValue n v
/-- Only actual original pair observations; no decoded validity or type premise. -/
def InternalValid : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (source target param tyA codeA tyB codeB ctx rest : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)) →
  (Nonempty (Derivation body Delta (graph3 (valid n) (numeral 1) source target param)) ↔
   Nonempty (Derivation body Delta
    (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx ⊓
      (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) codeA ⊓
       graph1 (OriginalCodeValidityGuard.check n) (numeral 1) codeB))))
/-- Full internal output equation, not merely a success-branch projection.
The actual guard is proved Boolean internally; no successful guard is assumed. -/
def InternalWindow : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (param ctx rest win table out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing ctx win table)) →
  (Nonempty (Derivation body Delta (graph1 (window n) out param)) ↔
   Nonempty (Derivation body Delta
    ((graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 0) ctx ⊓ eqn out (numeral 0)) ⊔
     (graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx ⊓ eqn out win))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalStructuralDecoderSuppliers.Targets
