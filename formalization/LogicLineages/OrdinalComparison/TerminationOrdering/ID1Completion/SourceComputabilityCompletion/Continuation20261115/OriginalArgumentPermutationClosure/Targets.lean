module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalArgumentPermutation.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114
/-- Symmetry of the literal optional-extraction permutation checker on arbitrary
raw numeric inputs. No extraction witness or count agreement is assumed. -/
def InternalSymmetry : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (source target : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) source target)) →
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) target source))

/-- Transitivity of the same original checker. Missing/malformed extractions
are handled by its actual Option guards, not a native validity assumption. -/
def InternalTransitivity : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (source middle target : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) source middle)) →
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) middle target)) →
  Nonempty (Derivation body Delta (graph2 OriginalArgumentPermutation.check (numeral 1) source target))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalArgumentPermutationClosure.Targets
