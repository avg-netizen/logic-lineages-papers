module

public import LogicLineages.ComputabilityKnowledge.RayUniformBounds

@[expose] public section

/-! Exact structural/numeric bound supplier for paper02 lem:ray. The generic
map clauses use only explicit original-map support/coefficient coverage, with
root, zero, and recursive-key coverage proved in this same target. No key
ordering, successful ray, eventual gap, or missing algorithm is a premise. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.RayUniformBounds

open ExponentialNormalForm ExponentialHereditaryCodec RayCoefficientCollection
open RayMapDifference RayFiniteSum
open LogicLineages.ComputabilityKnowledge.RayUniformBounds

def SourceBounds : Prop :=
  ∀ (d H : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d H n) →
    (∀ n ∈ ns, HereditaryWidth H (formDecode d H n) (widthBound H ns) ∧
      Covered d H ns H (formDecode d H n)) ∧
    (∀ k, HereditaryWidth k (zeroForm (d := d) k) (widthBound H ns) ∧
      Covered d H ns k (zeroForm k))

def RecursiveKeyBounds : Prop :=
  ∀ (d H : Nat) (ns : List Nat) (k : Nat) (f : Form d (k + 1)),
    HereditaryWidth (k + 1) f (widthBound H ns) → Covered d H ns (k + 1) f →
      ∀ key ∈ f.support,
        HereditaryWidth k key (widthBound H ns) ∧ Covered d H ns k key

def ActualAffineBound : Prop :=
  ∀ (d H : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d H n) →
    ∀ a : Affine d, FamilyCoefficient d H ns a →
      affineSize d H ns a ≤ weightMass d H ns

def ActualMassBound : Prop :=
  ∀ (d H : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d H n) →
    ∀ (k : Nat) (f g : Form d (k + 1)),
      HereditaryWidth (k + 1) f (widthBound H ns) →
      HereditaryWidth (k + 1) g (widthBound H ns) →
      Covered d H ns (k + 1) f → Covered d H ns (k + 1) g →
      ∀ s : Finset (Form d k), s ⊆ keySet f g →
        coefficientMass s
          (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g)
          (constantDifference f g) ≤ massBound d H ns

def CommonDominanceThreshold : Prop :=
  ∀ (d H : Nat) (ns : List Nat), (∀ n ∈ ns, CodeCanonical d H n) →
    sharedCutoff H ns ≤ commonThreshold d H ns ∧ 4 ≤ commonThreshold d H ns ∧
    ∀ (k : Nat) (f g : Form d (k + 1)),
      HereditaryWidth (k + 1) f (widthBound H ns) →
      HereditaryWidth (k + 1) g (widthBound H ns) →
      Covered d H ns (k + 1) f → Covered d H ns (k + 1) g →
      ∀ s : Finset (Form d k), s ⊆ keySet f g →
        RayDominance.threshold (coefficientMass s
          (slopeDifference (fun i => (sharedWeights d H ns).getD i.val 0) f g)
          (constantDifference f g)) ≤ commonThreshold d H ns

def ActualUniformPrograms : Prop :=
  Primrec (fun p : Nat × List Nat => widthBound p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => weightMass p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => massBound p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => commonThreshold p.1 p.2.1 p.2.2)

def Target : Prop := SourceBounds ∧ RecursiveKeyBounds ∧ ActualAffineBound ∧
  ActualMassBound ∧ CommonDominanceThreshold ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.RayUniformBounds
