module

public import LogicLineages.ComputabilityKnowledge.PositiveExpression
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProduct

@[expose] public section

/-! Literal finite-syntax normalization into the hereditary finite-map model.
The height parameter is an available bound, not a bound computed by a theorem
oracle. Addition recurses at the same height; an exponential product recurses
one level lower. The insufficient-height branch is explicit and is excluded
by the separately stated correctness theorem. Effective numerical coding is
still a separate obligation from this mathematical finite-map definition.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalizer

open PositiveExpression ExponentialNormalForm ExponentialNormalFormProduct

noncomputable section

def affineVariable {d : Nat} (i : Fin d) : Affine d :=
  Fin.cases 0 (fun j => if j = i then 1 else 0)

def variableForm {d : Nat} (h : Nat) (i : Fin d) : Form d h :=
  match h with
  | 0 => affineVariable i
  | h + 1 => Finsupp.single (zeroForm h) (affineVariable i)

def normalizeAt {d : Nat} : Expr (Fin d) → (h : Nat) → Form d h
  | .one, h => constantForm h 1
  | .var i, h => variableForm h i
  | .add a b, h => addForm h (normalizeAt a h) (normalizeAt b h)
  | .emul _ _, 0 => zeroForm 0
  | .emul a b, h + 1 => exponentialProduct h (normalizeAt a h) (normalizeAt b h)

def normalize {d : Nat} (a : Expr (Fin d)) : Form d a.depth :=
  normalizeAt a a.depth

end

end LogicLineages.ComputabilityKnowledge.ExponentialNormalizer
