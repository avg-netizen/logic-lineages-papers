module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalForm
public import Mathlib.Computability.Primrec.List

@[expose] public section

/-! Explicit numerical affine-vector codes and canonical finite-map codes.
All executable operations below are list/natural-number operations. Their
faithfulness to the mathematical finite maps and genuine primitive-recursive
certificates are separate conclusions, not fields or assumptions. Map keys
here are natural codes; the recursive hereditary-key refinement is separate.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec

open ExponentialNormalForm

abbrev CoeffCode := List Nat
abbrev MapCode := List (Nat × CoeffCode)

def coeffDecode (d : Nat) (xs : CoeffCode) : Affine d :=
  fun i => xs.getD i.val 0

def coeffNormalize (d : Nat) (xs : CoeffCode) : CoeffCode :=
  (List.range (d + 1)).map (fun i => xs.getD i 0)

def coeffConstant (d n : Nat) : CoeffCode :=
  (List.range (d + 1)).map (fun i => if i = 0 then n else 0)

def coeffVariable (d i : Nat) : CoeffCode :=
  (List.range (d + 1)).map (fun j => if j = i + 1 then 1 else 0)

def coeffAdd (d : Nat) (xs ys : CoeffCode) : CoeffCode :=
  (List.range (d + 1)).map (fun i => xs.getD i 0 + ys.getD i 0)

def coeffScale (d k : Nat) (xs : CoeffCode) : CoeffCode :=
  (List.range (d + 1)).map (fun i => k * xs.getD i 0)

def coeffRemove (d : Nat) (xs : CoeffCode) : CoeffCode :=
  (List.range (d + 1)).map (fun i => if i = 0 then 0 else xs.getD i 0)

def coeffIsZero (d : Nat) (xs : CoeffCode) : Bool :=
  decide (coeffNormalize d xs = coeffConstant d 0)

def CoeffCanonical (d : Nat) (xs : CoeffCode) : Prop :=
  xs.length = d + 1

def insertRaw (d key : Nat) (coeff : CoeffCode) : MapCode → MapCode
  | [] => [(key, coeff)]
  | (j, a) :: rest =>
      if key < j then (key, coeff) :: (j, a) :: rest
      else if key = j then (key, coeffAdd d coeff a) :: rest
      else (j, a) :: insertRaw d key coeff rest

def insertEntry (d key : Nat) (coeff : CoeffCode) (es : MapCode) : MapCode :=
  if coeffIsZero d coeff then es else insertRaw d key (coeffNormalize d coeff) es

def normalizeMap (d : Nat) (es : MapCode) : MapCode :=
  es.foldr (fun e acc => insertEntry d e.1 e.2 acc) []

def MapCanonical (d : Nat) (es : MapCode) : Prop :=
  es.Pairwise (fun a b => a.1 < b.1) ∧
    ∀ e ∈ es, CoeffCanonical d e.2 ∧ coeffIsZero d e.2 = false

noncomputable def mapDecode (d : Nat) (es : MapCode) : Nat →₀ Affine d :=
  es.foldr (fun e acc => Finsupp.single e.1 (coeffDecode d e.2) + acc) 0

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec
