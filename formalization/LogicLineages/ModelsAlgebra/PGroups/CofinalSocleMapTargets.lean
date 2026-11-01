module
public import LogicLineages.ModelsAlgebra.PGroups.LocalSocleBFDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.DivisibleExtensionDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
/-- ONE actual hom is simultaneously surjective on the actual p-socles
of ALL stages below the countable cut. Infinite source socles and actual
target divisibility are the literal hypotheses; a dense-map field is not. -/
def cofinalSocleSurjectiveHom : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (B C:Type) [AddCommGroup B] [AddCommGroup C]
    [Countable B] [Countable C] (δ:Ordinal.{0}) [Countable δ.ToType],
    0<δ → GroupDivisible C → SoclesInfiniteBelow p B δ →
    ∃f:B→+C,∀β:Ordinal.{0},β<δ →
      ∀c:pSocle p (⊤:AddSubgroup C),
        ∃b:pSocle p (transfiniteFiltration p β:AddSubgroup B),f (b:B)=(c:C)
end LogicLineages.ModelsAlgebra.PGroups.Targets
