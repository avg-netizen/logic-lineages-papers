module

public import LogicLineages.ComputabilityKnowledge.WWGroundClasses
public import LogicLineages.ComputabilityKnowledge.WWFiniteEnvelope

@[expose] public section

/-! Literal paper02 bounded-vector construction and original WW Definition
2.8 relations. Source vectors are nonempty finite lists, with zero at every
index beyond their level. Strict comparison is strict at index0 and weak at
all positive indices, not lexicographic order. -/
namespace LogicLineages.ComputabilityKnowledge.WWBoundedVectorPadding

open PositiveExpression WWOrdinalTermSemantics WWGroundAdmissibility WWGroundClasses

def component {d : Nat} (xs : List (Term (Fin d))) (i : Nat) : Term (Fin d) := xs.getD i .zero

noncomputable def VectorLE {d : Nat} (xs ys : List (Term (Fin d))) : Prop :=
  ∀ i : Nat, Comparison true (component xs i) (component ys i)

noncomputable def VectorLT {d : Nat} (xs ys : List (Term (Fin d))) : Prop :=
  Comparison false (component xs 0) (component ys 0) ∧
    ∀ i : Nat, 0 < i → Comparison true (component xs i) (component ys i)

noncomputable def VectorBoundedNorm {d : Nat} (xs : List (Term (Fin d))) : Prop :=
  ∀ i : Nat, NormComparison true (component xs i) (component xs 0)

def CVector {d : Nat} (xs : List (Term (Fin d))) : Prop :=
  xs ≠ [] ∧ ∀ i : Nat, i < xs.length → C d i (component xs i)

def remainder {d : Nat} (u v : Expr (Fin d)) : Expr (Fin d) := .add (.add u v) .one

def control {d : Nat} (u v : Expr (Fin d)) : Expr (Fin d) :=
  WWFiniteEnvelope.envelope d (remainder u v)

def head {d : Nat} (u v : Expr (Fin d)) : Term (Fin d) :=
  .collapse (embed (remainder u v)) (embed (control u v))

def left {d : Nat} (u v : Expr (Fin d)) : List (Term (Fin d)) := [head u v, embed (.add v .one)]
def weakRight {d : Nat} (u v : Expr (Fin d)) : List (Term (Fin d)) := [head u v, embed u]
def strictRight {d : Nat} (u v : Expr (Fin d)) : List (Term (Fin d)) := [.add (head u v) .one, embed u]

end LogicLineages.ComputabilityKnowledge.WWBoundedVectorPadding
