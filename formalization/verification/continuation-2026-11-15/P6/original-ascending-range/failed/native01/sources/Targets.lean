module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open TwoSol20261113.CalibratedPrimary.Membership (contains)
/-- Original List Nat Encodable codec and literal ascending List.range on every
input, not an unordered set or a descending enumeration. -/
def NativeRange : Prop := ∀ (v : List.Vector Nat 1),
  evaluate range v = Encodable.encode (List.range (v.get 0))
/-- Actual object-language range output membership is exactly strict index
boundedness. No decoded-list image, supplied length, validity, or membership
premise is assumed; all graph outputs and all raw indices are quantified. -/
def InternalMembership : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (bound out index : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 range out bound)) →
  (Nonempty (Derivation body Delta (graph2 contains (numeral 1) out index)) ↔
   Nonempty (Derivation body Delta (InternalLessThan.strictLess index bound)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalAscendingRange.Targets
