module

public import LogicLineages.ModelsAlgebra.PGroups.InfinitaryDefinitions

@[expose] public section

/-! Explicit ordinary group-language formulas for paper01 lines 184–188.
The image is described by literal natural-multiple terms, finite distinctness
conditions, existential blocks, and a countable universal conjunction. Neither
image infinitude nor a definability theorem is built into syntax/realization. -/
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary

open GroupBackAndForth

/-- Literal repeated addition in the existing original-language term syntax. -/
def multipleTerm {n : ℕ} : ℕ → GroupTerm n → GroupTerm n
  | 0, _ => .zero
  | c + 1, t => .add (multipleTerm c t) t

/-- Finite conjunction, including the true empty conjunction. -/
def finiteAnd {n : ℕ} : (m : ℕ) → (Fin m → QF n) → QF n
  | 0, _ => .neg .falsum
  | m + 1, f => .and (f 0) (finiteAnd m (fun i => f i.succ))

/-- Pairwise distinct c-multiples of the m newly bound variables. Existing
n free variables are untouched; diagonal pairs contribute the true formula. -/
def distinctMultipleMatrix (c n m : ℕ) : QF (n + m) :=
  finiteAnd m fun i => finiteAnd m fun j =>
    if i = j then .neg .falsum else
      .neg (.equal (multipleTerm c (.var (Fin.natAdd n i)))
        (multipleTerm c (.var (Fin.natAdd n j))))

/-- A singleton existential disjunction, with exactly m finite witnesses. -/
def distinctMultiples (c n m : ℕ) : Formula n :=
  .disjEx {0} (fun _ => m) (fun _ => .qf (distinctMultipleMatrix c n m))

/-- A literal countable conjunction of the finite-witness formulas, with
zero outer universal variables. Includes m=0 without a nonemptiness shortcut. -/
def infiniteMultipleImage (c : ℕ) : Formula 0 :=
  .conjAll Set.univ (fun _ => 0) (fun i => distinctMultiples c 0 i.val)

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
