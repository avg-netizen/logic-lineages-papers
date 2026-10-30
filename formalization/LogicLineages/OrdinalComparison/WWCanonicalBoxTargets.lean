module
public import LogicLineages.OrdinalComparison.WWCanonicalBoxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def ActualOrdinalNumeral : Prop :=
  (∀ (Γ : List Ty) (ρ : OrdinalComponent Γ → Ordinal.{0}) (n : Nat),
    denote ρ (ordinalNumeral n) = (n : Ordinal)) ∧
  (∀ (Γ : List Ty) (i n : Nat), 0 < n → GeneratedOrdinalGrade Γ i (ordinalNumeral n))

def ActualCanonicalBoxEquations : Prop :=
  ∀ (Γ : List Ty) (m n : Nat), n < m →
    ∀ (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
      (∀ i : Fin (m + 1), n < i.val → ordinalCanonicalBox f g i = f i) ∧
      (∀ i : Fin (m + 1), 0 < i.val → i.val ≤ n →
        ordinalCanonicalBox f g i =
          .emul (ordinalVectorAt (ordinalCanonicalBox f g) (i.val + 1))
            (.add (f i) (ordinalVectorAt g i.val))) ∧
      (ordinalCanonicalBox f g 0 =
        .collapse (ordinalVectorAt (ordinalCanonicalBox f g) 1)
          (ordinalBoxScalarTail n (f 0) (g 0)))

def ActualCanonicalBoxGeneratedGrade : Prop :=
  ∀ (Γ : List Ty) (m n : Nat), n < m →
    ∀ (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
      (∀ i, GeneratedOrdinalGrade Γ i.val (f i)) →
      (∀ i, GeneratedOrdinalGrade Γ i.val (g i)) →
      ∀ i, GeneratedOrdinalGrade Γ i.val (ordinalCanonicalBox f g i)

end LogicLineages.OrdinalComparison.Source.Targets
