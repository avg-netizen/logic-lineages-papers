module
public import LogicLineages.ModelsAlgebra.PGroups.SourceTwoInfiniteTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.Targets
open GroupInfinitary
universe u v

def groupSigmaScottIsomorphism : Prop :=
  ∀ (α : Ordinal.{v}) (G H : Type u) [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (φ : Formula 0), Complexity .sigma α φ →
      (GroupScottSentence G φ ↔ GroupScottSentence H φ)

def groupReservoirNoSigmaThreeScott : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (A : Type) [AddCommGroup A] [Countable A] (ell m : ℕ),
    0 < ell → ell < m →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p (ell-1) : AddSubgroup A)) = 0 →
    ∀ φ : Formula 0, Complexity .sigma (3 : Ordinal.{0}) φ →
      ¬ GroupScottSentence (ReservoirGroup A (ZMod (p^ell)) (ZMod (p^m))) φ

def groupRawSourceTwoInfiniteNoSigmaThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (G : Type) [AddCommGroup G] [Countable G] (N : ℕ)
    (a b : Fin N), a < b → (∀ x : G, p^N • x = 0) →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p a.val : AddSubgroup G)) = Cardinal.aleph0 →
    Module.rank (ZMod p) (UlmLayer p (finiteFiltration p b.val : AddSubgroup G)) = Cardinal.aleph0 →
    ∀ φ : Formula 0, Complexity .sigma (3 : Ordinal.{0}) φ →
      ¬ RawScottSentence (RawGroupStructure.ofGroup G) φ

end LogicLineages.ModelsAlgebra.PGroups.Targets
