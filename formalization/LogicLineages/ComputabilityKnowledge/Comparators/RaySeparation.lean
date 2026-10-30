module

public import LogicLineages.ComputabilityKnowledge.RaySeparation

@[expose] public section

/-! Exact full paper02 lem:ray target: heterogeneous original source family,
actual recursive support closure plus zeros, one positive effective ray,
explicit common threshold, computed eventual signs, and constant-free gap.
No calibration, ordering, separation, or computability oracle is a premise.
Source structural equality across height bounds uses the original proved
common-height embeddings, not equality of numerical functions. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RaySeparation

open ExponentialNormalForm ExponentialHereditaryCodec RayFamilyClosure
open LogicLineages.ComputabilityKnowledge.RaySeparation

def ActualClosedFamily : Prop :=
  ∀ (d : Nat) (roots : List HeightCode), SourceFamily d roots →
    (∀ p ∈ roots, p ∈ closedFamily d roots) ∧
    (∀ k, k ≤ maxHeight roots → (k, zeroCode d k) ∈ closedFamily d roots) ∧
    (∀ p ∈ closedFamily d roots, p.1 ≤ maxHeight roots ∧
      CodeCanonical d p.1 p.2 ∧ WellFormed p.1 (formDecode d p.1 p.2)) ∧
    (∀ k n, (k + 1, n) ∈ closedFamily d roots →
      ∀ key ∈ (formDecode d (k + 1) n).support,
        ∃ m, (k, m) ∈ closedFamily d roots ∧ formDecode d k m = key)

def PositiveEffectiveRay : Prop :=
  ∀ (d : Nat) (roots : List HeightCode),
    (weights d roots).length = d ∧ 0 < threshold d roots ∧
    ∀ i : Fin d, 0 < (weights d roots).getD i.val 0 ∧
      ∀ t, threshold d roots ≤ t → 0 < (weights d roots).getD i.val 0 * t

def ComputedEventualSigns : Prop :=
  (∀ (d : Nat) (roots : List HeightCode) (p q : HeightCode), signCode d roots p q ≤ 2) ∧
  ∀ (d : Nat) (roots : List HeightCode), SourceFamily d roots →
    ∀ p ∈ closedFamily d roots, ∀ q ∈ closedFamily d roots,
      ∀ t, threshold d roots ≤ t →
        (signCode d roots p q = 0 ↔ CommonHeightEqual d (maxHeight roots) p q) ∧
        (signCode d roots p q = 1 ↔ originalValue d roots p t < originalValue d roots q t) ∧
        (signCode d roots p q = 2 ↔ originalValue d roots q t < originalValue d roots p t)

def ConstantFreeGap : Prop :=
  ∀ (d : Nat) (roots : List HeightCode), SourceFamily d roots →
    ∀ p ∈ closedFamily d roots, ∀ q ∈ closedFamily d roots,
      constantCoefficient p.1 (formDecode d p.1 p.2) = 0 →
      constantCoefficient q.1 (formDecode d q.1 q.2) = 0 →
      ¬CommonHeightEqual d (maxHeight roots) p q →
      ∀ t, threshold d roots ≤ t →
        (signCode d roots p q = 1 → originalValue d roots p t + t ≤ originalValue d roots q t) ∧
        (signCode d roots p q = 2 → originalValue d roots q t + t ≤ originalValue d roots p t)

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × List HeightCode => weights p.1 p.2) ∧
  Primrec (fun p : Nat × List HeightCode => threshold p.1 p.2) ∧
  Primrec (fun p : Nat × List HeightCode × Nat => rayList p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List HeightCode × HeightCode × HeightCode =>
    signCode p.1 p.2.1 p.2.2.1 p.2.2.2)

def Target : Prop := ActualClosedFamily ∧ PositiveEffectiveRay ∧ ComputedEventualSigns ∧
  ConstantFreeGap ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.RaySeparation
