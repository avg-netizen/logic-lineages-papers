module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All-raw AST behavior and well-founded rank, independent of valid Code interpretation. -/
def RawDependency : Prop :=
  (∀ raw param, evaluate dependency (List.Vector.ofFn ![raw,param]) =
    NumberedMultisetNumeric.numbersNumber (rawChildren raw)) ∧
  (∀ raw child, child ∈ rawChildren raw → child < raw)
/-- Concrete literal frontier remains in the image of original Code encoding.
Order and duplicates are retained; no decoder or native-to-internal reflection. -/
def ValidFrontier : Prop := ∀ (n : Nat) (seed : NumberedAuxiliaryCoding.Code (Fin n))
    (depth param : Nat),
  evaluate (ExchangeFrontier.bindList dependency)
    (List.Vector.ofFn ![depth,NumberedLeastCodeRepresentative.codeNumber seed,param]) =
  NumberedMultisetNumeric.numbersNumber
    ((originalFrontier seed depth).map NumberedLeastCodeRepresentative.codeNumber)
def OriginalRankExhaustion : Prop := ∀ (n : Nat) (seed : NumberedAuxiliaryCoding.Code (Fin n)),
  (∀ depth child, child ∈ originalFrontier seed depth →
    NumberedLeastCodeRepresentative.codeNumber child + depth ≤ NumberedLeastCodeRepresentative.codeNumber seed) ∧
  originalFrontier seed (NumberedLeastCodeRepresentative.codeNumber seed + 1) = []
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesFrontier.Targets
