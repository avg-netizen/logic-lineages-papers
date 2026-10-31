module
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleCharacteristicDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
def divisiblePartCharacteristic : Prop :=
  ∀ (G H : Type) [AddCommGroup G] [AddCommGroup H] (e : G ≃+ H),
    ∃ d : divisiblePart G ≃+ divisiblePart H, ∀ x, (d x:H) = e (x:G)
def reducedDivisibleProductPart : Prop :=
  ∀ (R D : Type) [AddCommGroup R] [AddCommGroup D],
    IsReducedAddGroup R → GroupDivisible D →
    ∃ d : D ≃+ divisiblePart (R × D), ∀ x, (d x:R × D) = (0,x)
def divisibleProductSocleInvariant : Prop :=
  ∀ (R S D E : Type) [AddCommGroup R] [AddCommGroup S] [AddCommGroup D] [AddCommGroup E],
    IsReducedAddGroup R → IsReducedAddGroup S → GroupDivisible D → GroupDivisible E →
    ∀ p : ℕ, Nonempty ((R × D) ≃+ (S × E)) →
      Nonempty (pSocle p (⊤ : AddSubgroup D) ≃+ pSocle p (⊤ : AddSubgroup E))
end LogicLineages.ModelsAlgebra.PGroups.Targets
