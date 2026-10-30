module
public import LogicLineages.ModelsAlgebra.PGroups.ImageCardinalityDefinitions
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

/-- An arbitrary original-language interpretation. No group laws are assumed. -/
structure RawGroupStructure (G : Type u) where
  zero : G
  neg : G → G
  add : G → G → G

def RawGroupStructure.ofGroup (G : Type u) [AddCommGroup G] : RawGroupStructure G :=
  ⟨0,Neg.neg,Add.add⟩

def rawTermEval {G : Type u} (R : RawGroupStructure G) {n : ℕ}
    (a : Fin n → G) : GroupTerm n → G
  | .var i => a i
  | .zero => R.zero
  | .neg s => R.neg (rawTermEval R a s)
  | .add s t => R.add (rawTermEval R a s) (rawTermEval R a t)

def QF.RawRealize {G : Type u} (R : RawGroupStructure G) {n : ℕ}
    (q : QF n) (a : Fin n → G) : Prop :=
  match q with
  | .equal s t => rawTermEval R a s = rawTermEval R a t
  | .falsum => False
  | .neg q => ¬ q.RawRealize R a
  | .and q r => q.RawRealize R a ∧ r.RawRealize R a

def Formula.RawRealize {G : Type u} (R : RawGroupStructure G) :
    {n : ℕ} → Formula n → (Fin n → G) → Prop
  | _, .qf q, a => q.RawRealize R a
  | _, .disjEx s m matrix, a => ∃ i : s, ∃ c : Fin (m i) → G,
      (matrix i).RawRealize R (append a c)
  | _, .conjAll s m matrix, a => ∀ i : s, ∀ c : Fin (m i) → G,
      (matrix i).RawRealize R (append a c)

def DifferenceFormula.RawRealize {G : Type u} (R : RawGroupStructure G) {n : ℕ}
    (d : DifferenceFormula n) (a : Fin n → G) : Prop :=
  d.sigmaPart.RawRealize R a ∧ d.piPart.RawRealize R a

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
