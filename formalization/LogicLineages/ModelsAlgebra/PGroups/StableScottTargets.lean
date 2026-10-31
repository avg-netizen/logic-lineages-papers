module
public import LogicLineages.ModelsAlgebra.PGroups.StableScottDefinitions
public import Mathlib.LinearAlgebra.Dimension.Basic
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
def stableGroupTableExact : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (N:ℕ) (entries:Fin N→Option ℕ) (socleEntry:Option ℕ),
    Complexity .pi (3:Ordinal.{0}) (stableGroupTable p N entries socleEntry) ∧
    ∀ (G:Type) [AddCommGroup G] [Countable G],
      (stableGroupTable p N entries socleEntry).Realize (Fin.elim0:Fin 0→G) ↔
      (∀x:G,∃k:ℕ,p^k • x=0) ∧ StableAt p G (N:Ordinal.{0}) ∧
      Module.rank (ZMod p) (pSocle p (finiteFiltration p N:AddSubgroup G)) =
        (match socleEntry with | none=>Cardinal.aleph0 | some m=>(m:Cardinal)) ∧
      ∀ j:Fin N, Module.rank (ZMod p) (UlmLayer p (finiteFiltration p j.val:AddSubgroup G)) =
        (match entries j with | none=>Cardinal.aleph0 | some m=>(m:Cardinal))
def stablePiThreeScott : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G] (N:ℕ),
    (∀x:G,∃k:ℕ,p^k • x=0) → StableAt p G (N:Ordinal.{0}) →
    ∃ φ:Formula 0, Complexity .pi (3:Ordinal.{0}) φ ∧ GroupScottSentence G φ
def stableRawPiThreeScott : Prop :=
  ∀ (p:ℕ) [Fact p.Prime] (G:Type) [AddCommGroup G] [Countable G] (N:ℕ),
    (∀x:G,∃k:ℕ,p^k • x=0) → StableAt p G (N:Ordinal.{0}) →
    ∃ φ:Formula 0, Complexity .pi (3:Ordinal.{0}) φ ∧ RawScottSentence (RawGroupStructure.ofGroup G) φ
end LogicLineages.ModelsAlgebra.PGroups.Targets
