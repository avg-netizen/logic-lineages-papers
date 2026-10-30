module

public import LogicLineages.ComputabilityKnowledge.RayCoefficientCollection

@[expose] public section

/-! Exact source coefficient-collection/calibration supplier for paper02
lem:ray. This does not assert the higher-height induction, an effective
normal-form comparison, or the full numbered ray lemma.
-/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayCoefficientCollection

open ExponentialNormalForm ExponentialNormalFormCodec ExponentialHereditaryCodec
open LogicLineages.ComputabilityKnowledge.RayCoefficientCollection

def LiteralCoverage : Prop :=
  ∀ (d h : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d h n) →
    ∀ a : Affine d, FamilyCoefficient d h ns a →
      ∃ c ∈ collected h ns, coeffDecode d c = a

def CommonPositiveRay : Prop :=
  ∀ (d h : Nat) (ns : List Nat),
    (sharedWeights d h ns).length = d ∧ 0 < sharedCutoff h ns ∧
    ∀ i : Fin d, 0 < (sharedWeights d h ns).getD i.val 0 ∧
      ∀ t, sharedCutoff h ns ≤ t → 0 < sharedRay d h ns t i

def CommonSlopeInjection : Prop :=
  ∀ (d h : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d h n) →
    ∀ a b : Affine d, FamilyCoefficient d h ns a → FamilyCoefficient d h ns b →
      ((∑ i : Fin d, a i.succ * (sharedWeights d h ns).getD i.val 0) =
        (∑ i : Fin d, b i.succ * (sharedWeights d h ns).getD i.val 0) ↔
        ∀ i : Fin d, a i.succ = b i.succ)

def CommonEventualComparison : Prop :=
  ∀ (d h : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d h n) →
    ∀ a b : Affine d, FamilyCoefficient d h ns a → FamilyCoefficient d h ns b →
      ∀ t, sharedCutoff h ns ≤ t →
        (affineValue a (sharedRay d h ns t) = affineValue b (sharedRay d h ns t) ↔
          a = b) ∧
        (affineValue a (sharedRay d h ns t) < affineValue b (sharedRay d h ns t) ↔
          affineValue a (sharedRay d h ns (sharedCutoff h ns)) <
            affineValue b (sharedRay d h ns (sharedCutoff h ns)))

def CommonConstantFreeGap : Prop :=
  ∀ (d h : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d h n) →
    ∀ a b : Affine d, FamilyCoefficient d h ns a → FamilyCoefficient d h ns b →
      a 0 = 0 → b 0 = 0 → a ≠ b → ∀ t : Nat,
        (affineValue a (sharedRay d h ns (sharedCutoff h ns)) <
            affineValue b (sharedRay d h ns (sharedCutoff h ns)) →
          affineValue a (sharedRay d h ns t) + t ≤ affineValue b (sharedRay d h ns t)) ∧
        (¬affineValue a (sharedRay d h ns (sharedCutoff h ns)) <
            affineValue b (sharedRay d h ns (sharedCutoff h ns)) →
          affineValue b (sharedRay d h ns t) + t ≤ affineValue a (sharedRay d h ns t))

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => coefficients p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => collected p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => sharedWeights p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat => sharedCutoff p.1 p.2)

def Target : Prop := LiteralCoverage ∧ CommonPositiveRay ∧ CommonSlopeInjection ∧
  CommonEventualComparison ∧ CommonConstantFreeGap ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.RayCoefficientCollection
