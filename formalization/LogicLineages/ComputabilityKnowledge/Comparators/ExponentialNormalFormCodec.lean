module

public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec

@[expose] public section

/-! Genuine canonical finite-code supplier for paper-02 normalization.
Coefficient vectors have fixed finite arity; maps use strictly increasing
natural keys and nonzero canonical coefficients. A candidate must prove that
numeric-key merging is primitive recursive and faithfully represents actual
finite-map merging. No classical Decidable instance substitutes for effectivity.
Hereditary key coding and the full term compiler remain separate obligations.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodec

open ExponentialNormalForm
open LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodec

def CoefficientSemantics : Prop :=
  ∀ (d : Nat) (xs ys : CoeffCode) (k n : Nat),
    coeffDecode d (coeffNormalize d xs) = coeffDecode d xs ∧
    coeffDecode d (coeffConstant d n) = affineConstant n ∧
    coeffDecode d (coeffAdd d xs ys) = coeffDecode d xs + coeffDecode d ys ∧
    coeffDecode d (coeffScale d k xs) = (fun i => k * coeffDecode d xs i) ∧
    coeffDecode d (coeffRemove d xs) = affineRemoveConstant (coeffDecode d xs) ∧
    (coeffIsZero d xs = true ↔ coeffDecode d xs = 0) ∧
    (∀ i : Fin d, coeffDecode d (coeffVariable d i.val) =
      Fin.cases 0 (fun j => if j = i then 1 else 0))

def CoefficientCanonicality : Prop :=
  (∀ (d : Nat) (xs ys : CoeffCode),
    CoeffCanonical d xs → CoeffCanonical d ys →
      (coeffDecode d xs = coeffDecode d ys ↔ xs = ys)) ∧
  (∀ (d : Nat) (xs ys : CoeffCode) (k n i : Nat),
    CoeffCanonical d (coeffNormalize d xs) ∧
    CoeffCanonical d (coeffConstant d n) ∧
    CoeffCanonical d (coeffAdd d xs ys) ∧
    CoeffCanonical d (coeffScale d k xs) ∧
    CoeffCanonical d (coeffRemove d xs) ∧
    CoeffCanonical d (coeffVariable d i))

def CanonicalMapRepresentation : Prop :=
  (∀ (d : Nat) (es : MapCode),
    MapCanonical d (normalizeMap d es) ∧
    mapDecode d (normalizeMap d es) = mapDecode d es) ∧
  (∀ (d : Nat) (es fs : MapCode),
    MapCanonical d es → MapCanonical d fs →
      (mapDecode d es = mapDecode d fs ↔ es = fs))

def ActualPrimitiveRecursion : Prop :=
  Primrec (fun p : Nat × CoeffCode => coeffNormalize p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => coeffConstant p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => coeffVariable p.1 p.2) ∧
  Primrec (fun p : Nat × CoeffCode × CoeffCode => coeffAdd p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × CoeffCode => coeffScale p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × CoeffCode => coeffRemove p.1 p.2) ∧
  Primrec (fun p : Nat × CoeffCode => coeffIsZero p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × CoeffCode × MapCode =>
    insertEntry p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × MapCode => normalizeMap p.1 p.2)

def Target : Prop := CoefficientSemantics ∧ CoefficientCanonicality ∧
  CanonicalMapRepresentation ∧ ActualPrimitiveRecursion

end LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormCodec
