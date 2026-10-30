module

public import LogicLineages.ModelsAlgebra.PGroups.ImageInfinitudeDefinitions
public import LogicLineages.ModelsAlgebra.PGroups.UlmDefinitions
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

/-! Literal finite Ulm lower-bound formulas, paper01 lines 190–198.
Index j denotes source j+1: the layer is (p^j G)[p]/(p^(j+1)G)[p].
All coefficient vectors over the actual finite field are enumerated. Zero is
skipped by a true QF clause; no independence or definability oracle occurs. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth
open scoped BigOperators
universe u

def finiteSumTerm {n : ℕ} : (m : ℕ) → (Fin m → GroupTerm n) → GroupTerm n
  | 0, _ => .zero
  | m + 1, f => .add (f 0) (finiteSumTerm m (fun i => f i.succ))

def ulmRootTerm (p j n m : ℕ) (i : Fin m) : GroupTerm ((n + m) + 1) :=
  multipleTerm (p ^ j) (.var (Fin.castAdd 1 (Fin.natAdd n i)))

def ulmCombinationTerm (p j n m : ℕ) (r : Fin m → ZMod p) : GroupTerm ((n + m) + 1) :=
  finiteSumTerm m (fun i => multipleTerm (r i).val (ulmRootTerm p j n m i))

noncomputable def ulmLowerMatrix (p : ℕ) [Fact p.Prime] (j n m : ℕ) :
    QF ((n + m) + 1) := by
  classical
  let coeff := (Fintype.equivFin (Fin m → ZMod p)).symm
  exact .and
    (finiteAnd m fun i => .equal (multipleTerm p (ulmRootTerm p j n m i)) .zero)
    (finiteAnd (Fintype.card (Fin m → ZMod p)) fun k =>
      if coeff k = 0 then .neg .falsum else
        .neg (.equal
          (multipleTerm (p ^ (j + 1)) (.var (Fin.natAdd (n + m) (0 : Fin 1))))
          (ulmCombinationTerm p j n m (coeff k))))

/-- Universal z rules out every nonzero coefficient combination being a
p^(j+1)-multiple. The socle conditions are repeated harmlessly for each z. -/
noncomputable def ulmLowerWitnessFormula (p : ℕ) [Fact p.Prime] (j n m : ℕ) : Formula (n + m) :=
  .conjAll {0} (fun _ => 1) (fun _ => .qf (ulmLowerMatrix p j n m))

/-- Actual Sigma_2 finite root witnesses, with a Pi_1 matrix. -/
noncomputable def ulmLowerFormula (p : ℕ) [Fact p.Prime] (j n m : ℕ) : Formula n :=
  .disjEx {0} (fun _ => m) (fun _ => ulmLowerWitnessFormula p j n m)

/-- An explicit algebraic root condition, not a definition of dimension or
independence. Its equivalence to genuine quotient independence is a theorem. -/
def IndependentRootWitnesses {G : Type u} [AddCommGroup G] (p j : ℕ) {m : ℕ}
    (d : Fin m → G) : Prop :=
  (∀ i, p • (p ^ j • d i) = 0) ∧
    ∀ r : Fin m → ZMod p, r ≠ 0 →
      (∑ i, (r i).val • (p ^ j • d i)) ∉ finiteFiltration p (j + 1)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
