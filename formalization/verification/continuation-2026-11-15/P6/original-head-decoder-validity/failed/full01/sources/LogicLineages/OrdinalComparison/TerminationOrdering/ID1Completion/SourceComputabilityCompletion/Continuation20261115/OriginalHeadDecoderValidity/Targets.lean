module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every raw input, including malformed basics, out-of-bound symbols and unknown tags. -/
def NativeDecoderValidity : Prop := ∀ (n raw : Nat),
  evaluate (check n) (List.Vector.ofFn ![raw]) =
    (NumberedNumericDecoding.decodeHeadNumber n raw).isSome.toNat
/-- Literal successful branches of the original head decoder, not a window predicate. -/
def allowed {alpha : Type} (n : Nat) (tag payload : OTerm alpha) : Formula alpha :=
  (((eqn tag (numeral 0) ⊔ eqn tag (numeral 1)) ⊓ eqn payload (numeral 0)) ⊔
    (eqn tag (numeral 2) ⊔ (eqn tag (numeral 3) ⊔
      (eqn tag (numeral 4) ⊔ (eqn tag (numeral 5) ⊓ InternalLessThan.strictLess payload (numeral n))))))
/-- An actual pair observation is the sole constructor evidence. No native decoding,
validity, type/window membership or hidden head witness is assumed. -/
def InternalAcceptedBranches : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw tag payload : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw tag payload)) →
  (Nonempty (Derivation body Delta (graph1 (check n) (numeral 1) raw)) ↔
    Nonempty (Derivation body Delta (allowed n tag payload)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalHeadDecoderValidity.Targets
