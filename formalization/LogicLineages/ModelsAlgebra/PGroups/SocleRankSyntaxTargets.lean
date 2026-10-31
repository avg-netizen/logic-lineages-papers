module
public import LogicLineages.ModelsAlgebra.PGroups.SocleRankSyntaxDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def socleUpperDimension : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (j n m:ℕ),
    Complexity .pi (1:Ordinal.{0}) (socleUpperFormula p j n m) ∧
    ∀ (G:Type) [AddCommGroup G] (a:Fin n→G),
      (socleUpperFormula p j n m).Realize a ↔
        Module.rank (ZMod p) (pSocle p (finiteFiltration p j:AddSubgroup G))≤(m:Cardinal)
def socleInfiniteDimension : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (j n:ℕ),
    Complexity .pi (2:Ordinal.{0}) (infiniteSocleFormula p j n) ∧
    ∀ (G:Type) [AddCommGroup G] (a:Fin n→G),
      (infiniteSocleFormula p j n).Realize a ↔
        Cardinal.aleph0≤Module.rank (ZMod p) (pSocle p (finiteFiltration p j:AddSubgroup G))
def countableSocleRankBound : Prop :=
  ∀ (p:ℕ) (G:Type) [AddCommGroup G] [Countable G] (S:AddSubgroup G),
    Module.rank (ZMod p) (pSocle p S)≤Cardinal.aleph0
def socleRankEntryExact : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (j n:ℕ) (entry:Option ℕ),
    Complexity .pi (2:Ordinal.{0}) (socleRankEntry p j n entry) ∧
    ∀ (G:Type) [AddCommGroup G] [Countable G] (a:Fin n→G),
      (socleRankEntry p j n entry).Realize a ↔
        Module.rank (ZMod p) (pSocle p (finiteFiltration p j:AddSubgroup G)) =
          (match entry with | none=>Cardinal.aleph0 | some m=>(m:Cardinal))
end LogicLineages.ModelsAlgebra.PGroups.Targets
