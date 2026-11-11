module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorEliminationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem firstTag1 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 1) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (query))) out xs)) := by
  have h1 := branchNumeralElim 1 1 (leftOf query) _ _ out xs ht ho
  exact h1

theorem firstTag2 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 2) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (query)))) out xs)) := by
  have h1 := branchNumeralElim 2 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 2 4 (leftOf query) _ _ out xs ht h1
  have h5 := branchNumeralElim 2 5 (leftOf query) _ _ out xs ht h4
  exact h5

theorem secondTag2 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 2) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf (query)))) out xs)) := by
  have h5 := branchNumeralElim 2 5 (leftOf query) _ _ out xs ht ho
  exact h5

theorem firstTag4 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 4) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (query))) out xs)) := by
  have h1 := branchNumeralElim 4 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 4 4 (leftOf query) _ _ out xs ht h1
  exact h4

theorem firstTag5 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 5) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (rightOf (rightOf (query)))))) out xs)) := by
  have h1 := branchNumeralElim 5 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 5 4 (leftOf query) _ _ out xs ht h1
  have h5 := branchNumeralElim 5 5 (leftOf query) _ _ out xs ht h4
  exact h5

theorem secondTag5 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 5) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf (rightOf (rightOf (rightOf (query))))))) out xs)) := by
  have h5 := branchNumeralElim 5 5 (leftOf query) _ _ out xs ht ho
  exact h5

theorem firstTag7 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 7) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (firstOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (leftOf (rightOf (rightOf (query)))) out xs)) := by
  have h1 := branchNumeralElim 7 1 (leftOf query) _ _ out xs ht ho
  have h4 := branchNumeralElim 7 4 (leftOf query) _ _ out xs ht h1
  have h5 := branchNumeralElim 7 5 (leftOf query) _ _ out xs ht h4
  exact h5

theorem secondTag7 {n : Nat} (query : Program n) (out : OTerm alpha) (xs : Fin n → OTerm alpha)
    (ht : Nonempty (Derivation body Delta (programGraph (leftOf query) (numeral 7) xs)))
    (ho : Nonempty (Derivation body Delta (programGraph (secondOf query) out xs))) :
    Nonempty (Derivation body Delta (programGraph (rightOf (rightOf (rightOf (query)))) out xs)) := by
  have h5 := branchNumeralElim 7 5 (leftOf query) _ _ out xs ht ho
  exact h5

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorEliminationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorEliminationProof
