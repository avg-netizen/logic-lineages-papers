module

public import LogicLineages.ComputabilityKnowledge.RayHeightInduction

@[expose] public section

/-! Source-family consequence of the actual height induction, paper02
lem:ray. Only canonical representation and original WellFormed hypotheses
occur; no structural bounds, pairwise gaps, or successful order are premises.
The explicit ray and threshold are inherited from checked finite programs.
This gate does not yet claim a primitive-recursive hereditary evaluator. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayHeightInduction

open ExponentialNormalForm ExponentialHereditaryCodec RayUniformBounds
open LogicLineages.ComputabilityKnowledge.RayHeightInduction

def StableEqualityAndOrder : Prop :=
  ∀ (d H : Nat) (ns : List Nat),
    (∀ n ∈ ns, CodeCanonical d H n) →
    (∀ n ∈ ns, WellFormed H (formDecode d H n)) →
    ∀ n ∈ ns, ∀ m ∈ ns, ∀ t, commonThreshold d H ns ≤ t →
      (rayValue d H ns H (formDecode d H n) t =
          rayValue d H ns H (formDecode d H m) t ↔
        formDecode d H n = formDecode d H m) ∧
      (rayValue d H ns H (formDecode d H n) t <
          rayValue d H ns H (formDecode d H m) t ↔
        rayValue d H ns H (formDecode d H n) (commonThreshold d H ns) <
          rayValue d H ns H (formDecode d H m) (commonThreshold d H ns))

def ConstantFreeOrientedGap : Prop :=
  ∀ (d H : Nat) (ns : List Nat),
    (∀ n ∈ ns, CodeCanonical d H n) →
    (∀ n ∈ ns, WellFormed H (formDecode d H n)) →
    ∀ n ∈ ns, ∀ m ∈ ns,
      constantCoefficient H (formDecode d H n) = 0 →
      constantCoefficient H (formDecode d H m) = 0 →
      formDecode d H n ≠ formDecode d H m →
      ∀ t, commonThreshold d H ns ≤ t →
        (rayValue d H ns H (formDecode d H n) (commonThreshold d H ns) <
            rayValue d H ns H (formDecode d H m) (commonThreshold d H ns) →
          rayValue d H ns H (formDecode d H n) t + t ≤
            rayValue d H ns H (formDecode d H m) t) ∧
        (¬rayValue d H ns H (formDecode d H n) (commonThreshold d H ns) <
            rayValue d H ns H (formDecode d H m) (commonThreshold d H ns) →
          rayValue d H ns H (formDecode d H m) t + t ≤
            rayValue d H ns H (formDecode d H n) t)

def Target : Prop := StableEqualityAndOrder ∧ ConstantFreeOrientedGap

end LogicLineages.ComputabilityKnowledge.Comparators.RayHeightInduction
