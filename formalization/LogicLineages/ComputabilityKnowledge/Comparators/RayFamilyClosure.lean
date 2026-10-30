module

public import LogicLineages.ComputabilityKnowledge.RayFamilyClosure

@[expose] public section

/-! Original finite family plus actual hereditary keys and zeros, including
empty-family behavior. Common-height equality is original map equality after
proved literal height embeddings, never numerical functional equivalence. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayFamilyClosure

open ExponentialNormalForm ExponentialHereditaryCodec
open LogicLineages.ComputabilityKnowledge.RayFamilyClosure

def IteratedHeightTransport : Prop :=
  ∀ (d h extra n : Nat),
    CodeCanonical d (h + extra) (raiseManyCode d h extra n) ∧
    formDecode d (h + extra) (raiseManyCode d h extra n) =
      raiseMany extra h (formDecode d h n)

def OriginalEmbeddingLaws : Prop :=
  ∀ (d h extra : Nat), Function.Injective (raiseMany (d := d) extra h) ∧
    ∀ f : Form d h,
      (∀ ρ, value (h + extra) (raiseMany extra h f) ρ = value h f ρ) ∧
      constantCoefficient (h + extra) (raiseMany extra h f) = constantCoefficient h f ∧
      (WellFormed h f → WellFormed (h + extra) (raiseMany extra h f))

def OriginalMembersAndZero : Prop :=
  ∀ (d : Nat) (roots : List HeightCode),
    (∀ p ∈ roots, p ∈ closedFamily d roots) ∧
    (∀ k, k ≤ maxHeight roots → (k, zeroCode d k) ∈ closedFamily d roots) ∧
    closedFamily d [] = [(0, zeroCode d 0)]

def ClosureBoundsAndValidity : Prop :=
  ∀ (d : Nat) (roots : List HeightCode), SourceFamily d roots →
    ∀ p ∈ closedFamily d roots, p.1 ≤ maxHeight roots ∧
      CodeCanonical d p.1 p.2 ∧ WellFormed p.1 (formDecode d p.1 p.2)

def ActualSupportClosure : Prop :=
  ∀ (d : Nat) (roots : List HeightCode), SourceFamily d roots →
    ∀ (k n : Nat), (k + 1, n) ∈ closedFamily d roots →
      ∀ key ∈ (formDecode d (k + 1) n).support,
        ∃ m, (k, m) ∈ closedFamily d roots ∧ formDecode d k m = key

def LiftedOriginalSemantics : Prop :=
  ∀ (d : Nat) (roots : List HeightCode), SourceFamily d roots →
    (∀ n ∈ liftedFamily d roots, CodeCanonical d (maxHeight roots) n ∧
      WellFormed (maxHeight roots) (formDecode d (maxHeight roots) n)) ∧
    ∀ p ∈ closedFamily d roots,
      liftCode d (maxHeight roots) p ∈ liftedFamily d roots ∧
      (∀ ρ, value (maxHeight roots) (formDecode d (maxHeight roots)
        (liftCode d (maxHeight roots) p)) ρ = value p.1 (formDecode d p.1 p.2) ρ) ∧
      constantCoefficient (maxHeight roots) (formDecode d (maxHeight roots)
        (liftCode d (maxHeight roots) p)) = constantCoefficient p.1 (formDecode d p.1 p.2)

def SameHeightStructuralEquality : Prop :=
  ∀ (d H h n m : Nat), h ≤ H →
    (CommonHeightEqual d H (h, n) (h, m) ↔ formDecode d h n = formDecode d h m)

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat => raiseManyCode p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat => descendants p.1 p.2) ∧
  Primrec maxHeight ∧
  Primrec (fun p : Nat × List HeightCode => closedFamily p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × HeightCode => liftCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List HeightCode => liftedFamily p.1 p.2)

def Target : Prop := IteratedHeightTransport ∧ OriginalEmbeddingLaws ∧ OriginalMembersAndZero ∧
  ClosureBoundsAndValidity ∧ ActualSupportClosure ∧ LiftedOriginalSemantics ∧
  SameHeightStructuralEquality ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.RayFamilyClosure
