module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.PGroups.Targets

open GroupBackAndForth GroupInfinitary
universe u v

/-- Rank-zero semantics is actual atomic/Boolean truth agreement. -/
def groupQFTruthAgreement : Prop :=
  ∀ (A B : Type u) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (a : Fin n → A) (b : Fin n → B),
    AtomicAgreement a b → ∀ q : QF n, q.Realize a ↔ q.Realize b

/-- Positive-rank Sigma padding is an actual syntactic construction with
unchanged truth, not an assumption that a QF leaf already has every rank. -/
def groupSigmaQFPadding : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 → ∀ (n : ℕ) (q : QF n),
    Complexity .sigma α (sigmaQF q) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (sigmaQF q).Realize a ↔ q.Realize a

def groupPiQFPadding : Prop :=
  ∀ (α : Ordinal.{v}), α ≠ 0 → ∀ (n : ℕ) (q : QF n),
    Complexity .pi α (piQF q) ∧
      ∀ (G : Type u) [AddCommGroup G] (a : Fin n → G),
        (piQF q).Realize a ↔ q.Realize a

/-- Paper01 Conventions: Pi truth transfers left to right and Sigma truth
right to left for the literal asymmetric relation. The statement holds over
all additive commutative groups, hence the original countable abelian
p-groups. It is a supplier, not a Scott-classification theorem. -/
def groupInfinitaryTruthTransfer : Prop :=
  ∀ (α : Ordinal.{v}) (A B : Type u) [AddCommGroup A] [AddCommGroup B]
    (n : ℕ) (a : Fin n → A) (b : Fin n → B), BackAndForth α a b →
      (∀ φ : Formula n, Complexity .pi α φ → φ.Realize a → φ.Realize b) ∧
      (∀ φ : Formula n, Complexity .sigma α φ → φ.Realize b → φ.Realize a)

end LogicLineages.ModelsAlgebra.PGroups.Targets
