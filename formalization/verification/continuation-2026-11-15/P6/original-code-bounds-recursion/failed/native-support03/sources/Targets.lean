module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Original codeBounds on every raw code, with the explicitly chosen invalid0
extension, not an upper bound/nodeCount or only encoded-image theorem. -/
def NativeBounds : Prop := ∀ (n : Nat) (v : List.Vector Nat 1),
  evaluate (bounds n) v = ((NumberedNumericDecoding.decodeCode n (v.get 0)).map
    (fun code => Encodable.encode (NumberedSyntaxBoundsPrimrec.codeBounds code))).getD 0
/-- Exact new totalized layer equation at a payload successor. No guard-success,
child-value validity or native image premise. -/
def InternalLayerEquation : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw answers param out : OTerm alpha),
  (Nonempty (Derivation body Delta (graph3 (layer n) (suc out) raw answers param)) ↔
   Nonempty (Derivation body Delta
    ((graph1 (OriginalCodeValidityGuard.check n) (numeral 0) raw ⊓ eqn out (numeral 0)) ⊔
     (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) raw ⊓
      graph2 (OriginalBoundsRecombination.recombine n) (suc out) raw answers))))
/-- Actual new bounds layer is present even for malformed inputs: Some0 is not
None. This is internal graph nonfailure, not borrowed argument-entry semantics. -/
def InternalLayerNonzero : Prop := ∀ (n : Nat) (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (raw answers param out : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (layer n) out raw answers param)) →
  Nonempty (Derivation body Delta (eqn out (numeral 0)).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.Targets
