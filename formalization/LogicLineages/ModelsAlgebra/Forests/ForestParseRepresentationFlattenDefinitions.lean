module
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCotreeDefinitions
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Logic.Equiv.Prod
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten
open RankedParse ForestParseRepresentationCotree

/-- A nonempty finite list of genuine cotrees, with occurrences retained. -/
structure Family where
  count : Nat
  positive : 0 < count
  child : Fin count → Cotree

def singletonFamily (t : Cotree) : Family := ⟨1, by decide, fun _ => t⟩

/-- Flatten exactly one matching operation root. Distinct operations remain intact. -/
def frontier (o : Operation) : Cotree → Family
  | .atom => singletonFamily .atom
  | t@(.node p n c) =>
      if p = o then ⟨n + 2, Nat.zero_lt_succ _, c⟩ else singletonFamily t

def concatenate (f g : Family) : Family where
  count := f.count + g.count
  positive := Nat.add_pos_left f.positive _
  child := fun k => Sum.elim f.child g.child (finSumFinEquiv.symm k)

def packNode (o : Operation) (f : Family) (h : 2 ≤ f.count) : Cotree :=
  .node o (f.count - 2) (fun i => f.child (Fin.cast (Nat.sub_add_cancel h) i))

def merge (o : Operation) (s t : Cotree) : Cotree :=
  packNode o (concatenate (frontier o s) (frontier o t))
    (Nat.add_le_add (frontier o s).positive (frontier o t).positive)

/-- Concrete recursive flattening of literal binary parses, with no graph oracle. -/
def normalize : RankedParse.Term → Cotree
  | .atom => .atom
  | .node o s t => merge o (normalize s) (normalize t)

/-- Exact sum/join semantics on arbitrary child graphs. -/
def operationGraph {V W : Type} (o : Operation) (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (Sum V W) where
  Adj
    | .inl x, .inl y => G.Adj x y
    | .inr x, .inr y => H.Adj x y
    | .inl _, .inr _ | .inr _, .inl _ => o = .join
  symm.symm
    | .inl _, .inl _ => G.adj_symm
    | .inr _, .inr _ => H.adj_symm
    | .inl _, .inr _ | .inr _, .inl _ => id
  loopless.irrefl
    | .inl _ => G.irrefl
    | .inr _ => H.irrefl

noncomputable def familyAdj {I : Type} (o : Operation) (c : I → Cotree)
    (x y : (i : I) × ForestParseRepresentationCotree.Leaf (c i)) : Prop := by
  classical
  exact if h : x.1 = y.1 then
    ForestParseRepresentationCotree.Adj (c y.1) (h ▸ x.2) y.2 else o = .join

noncomputable def familyGraph {I : Type} (o : Operation) (c : I → Cotree) :
    SimpleGraph ((i : I) × ForestParseRepresentationCotree.Leaf (c i)) where
  Adj := familyAdj o c
  symm.symm := by
    rintro ⟨i, x⟩ ⟨j, y⟩ h
    by_cases hij : i = j
    · subst j
      simp [familyAdj] at h ⊢
      exact ForestParseRepresentationCotree.adjSymm (c i) x y h
    · simpa [familyAdj, hij, Ne.symm hij] using h
  loopless.irrefl := by
    rintro ⟨i, x⟩
    simpa [familyAdj] using ForestParseRepresentationCotree.adjIrrefl (c i) x

end LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationFlatten
