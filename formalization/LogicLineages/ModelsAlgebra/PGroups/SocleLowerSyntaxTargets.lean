module
public import LogicLineages.ModelsAlgebra.PGroups.SocleLowerSyntaxDefinitions
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary GroupBackAndForth

def socleLowerMatrixRealization : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] (j n m:ℕ)
    (a:Fin n→G) (d:Fin m→G),
    (socleLowerMatrix p j n m).Realize (append a d) ↔ SocleRootWitnesses p j d
def socleRootRepresentatives : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] (j m:ℕ),
    (∃ d:Fin m→G,SocleRootWitnesses p j d) ↔
      ∃ v:Fin m→pSocle p (finiteFiltration p j:AddSubgroup G), LinearIndependent (ZMod p) v
def socleLowerDimension : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (j n m:ℕ),
    Complexity .sigma (1:Ordinal.{0}) (socleLowerFormula p j n m) ∧
    ∀ (G:Type) [AddCommGroup G] (a:Fin n→G),
      (socleLowerFormula p j n m).Realize a ↔
        (m:Cardinal)≤Module.rank (ZMod p) (pSocle p (finiteFiltration p j:AddSubgroup G))
end LogicLineages.ModelsAlgebra.PGroups.Targets
