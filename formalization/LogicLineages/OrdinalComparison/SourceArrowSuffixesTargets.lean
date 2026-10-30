module
public import LogicLineages.OrdinalComparison.SourceArrowSuffixesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceArrowSuffixesTargets
open SourceArrowSuffixes SourceSpecialApplication

def ExactArrowSuffixEnumeration : Prop := ∀ (σ : Ty) (args : List Ty) (τ : Ty),
    (args, τ) ∈ arrowSuffixes σ ↔ args ≠ [] ∧ arrows args τ = σ

def ArrowSuffixSubtypes : Prop := ∀ (σ : Ty) (args : List Ty) (τ : Ty),
    (args, τ) ∈ arrowSuffixes σ → τ ∈ σ.subtypes ∧ ∀ ρ ∈ args, ρ ∈ σ.subtypes

def ArrowSuffixStrictSize : Prop := ∀ (σ : Ty) (args : List Ty) (τ : Ty),
    (args, τ) ∈ arrowSuffixes σ → typeSize τ < typeSize σ ∧
      ∀ ρ ∈ args, typeSize ρ < typeSize σ

def ArrowSuffixNoDuplicates : Prop := ∀ σ : Ty, (arrowSuffixes σ).Nodup
end LogicLineages.OrdinalComparison.Source.SourceArrowSuffixesTargets
