module
public import LogicLineages.PermittedControl.EntryDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Exact computable partial first-entry program for actual normal inputs.
Every successful result is the genuine first hit; skipped targets are not totalized. -/
def EntryEffectivity : Prop := ∀ (f : Nat → Nat), Computable f →
  Partrec (entryPartialWith f) ∧
  ∀ (a nu : NONote), (nu.1.repr = 0 ∨ Order.IsSuccLimit nu.1.repr) →
    ∀ (E i : Nat), (E,i) ∈ entryPartialWith f (rawNoteEncode a.1, rawNoteEncode nu.1) ↔
      FirstEntry f a.1.repr nu.1.repr i ∧ E = entryNormAt f a.1.repr i

/-- The sufficient affordable tail and exact orbit, without an entry oracle. -/
def EntryExistenceOrbit : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (lam nu : Ordinal.{0}) (t : Nat), lam < epsilonZero → Order.IsSuccLimit lam →
    (nu = 0 ∨ Order.IsSuccLimit nu) → nu < lam →
    max 2 (max (actualOrdinalNorm lam) (actualOrdinalNorm nu)) ≤ t →
    ∃ i : Nat, FirstEntry f (countInitial lam t) nu i ∧
      entryNormAt f (countInitial lam t) i = f^[i] t

/-- Full prop:entry-residues: exact finite omega-tail and complementary proper
interval cases, explicit stated tail, actual first hit and signed residues. -/
def EntryResidues : Prop := ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m : Nat) (lam nu : Ordinal.{0}) (t : Nat), 0 < m → lam < epsilonZero →
    Order.IsSuccLimit lam → (nu = 0 ∨ Order.IsSuccLimit nu) → nu < lam →
    max (actualOrdinalNorm lam) (max (actualOrdinalNorm nu + 3) (max m B)) ≤ t →
    ∃ i : Nat, FirstEntry f (countInitial lam t) nu i ∧
      entryNormAt f (countInitial lam t) i = f^[i] t ∧
      (∀ k : Nat, 0 < k → lam = nu + Ordinal.omega0 * (k : Ordinal) → i = k) ∧
      ((¬ ∃ k : Nat, 0 < k ∧ lam = nu + Ordinal.omega0 * (k : Ordinal)) →
        Int.ModEq (m : Int) (i : Int) ((potential t : Int) - (((actualOrdinalNorm nu + 1) / 2 : Nat) : Int)) ∧
        Int.ModEq (2 * (m : Int)) (entryNormAt f (countInitial lam t) i : Int)
          (2 * (((actualOrdinalNorm nu + 1) / 2 : Nat) : Int)))

end LogicLineages.PermittedControl.Targets
