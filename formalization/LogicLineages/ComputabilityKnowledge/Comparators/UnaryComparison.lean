module

public import LogicLineages.ComputabilityKnowledge.UnaryComparison

@[expose] public section

/-! Exact full source unary theorem: one original positive ground variable,
arbitrary finite exponential depth, both strict and weak universal relations,
actual least positive counterexamples, exact parser rejection, and genuine
uniform programs. The finite threshold is inherited from proved separation. -/
namespace LogicLineages.ComputabilityKnowledge.Comparators.UnaryComparison

open PositiveExpression ExponentialNormalForm ExponentialHereditaryCodec
open CircuitReduction FiniteComparisonEnumeration RayFamilyClosure
open LogicLineages.ComputabilityKnowledge.UnaryComparison

def UnaryRayIdentity : Prop :=
  (∀ roots : List HeightCode, RaySeparation.weights 1 roots = [1]) ∧
  ∀ (roots : List HeightCode) (p : HeightCode) (t : Nat),
    RaySeparation.originalValue 1 roots p t = value p.1 (formDecode 1 p.1 p.2) (fun _ => t) ∧
    RayCodeEvaluation.evalCode 1 p.1 p.2 [t] = value p.1 (formDecode 1 p.1 p.2) (fun _ => t)

def ExactFiniteScan : Prop :=
  ∀ (weak : Bool) (pq : HeightCode × HeightCode) (T : Nat),
    (firstFailure weak pq T = none ↔ ∀ n, 0 < n → n ≤ T → holdsAt weak pq n = true) ∧
    ∀ n, firstFailure weak pq T = some n ↔
      0 < n ∧ n ≤ T ∧ holdsAt weak pq n = false ∧
        ∀ m, 0 < m → m < n → holdsAt weak pq m = true

def ProvedEventualComparison : Prop :=
  ∀ (weak : Bool) (pq : HeightCode × HeightCode), SourceFamily 1 [pq.1, pq.2] →
    0 < boundCode pq ∧ ∀ n, boundCode pq ≤ n →
      holdsAt weak pq n = holdsAt weak pq (boundCode pq)

def ExactRawDomain : Prop :=
  ∀ (weak : Bool) (a b : List Nat),
    (resultCode weak a b).isSome = ((decodeExpr 1 a).isSome && (decodeExpr 1 b).isSome) ∧
    (decisionCode weak a b).isSome = ((decodeExpr 1 a).isSome && (decodeExpr 1 b).isSome)

def SourceResult : Prop :=
  ∀ (weak : Bool) (a b : Expr (Fin 1)),
    (resultCode weak (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some none ↔ ∀ n : PosNat, Holds weak a b n) ∧
    ∀ n, resultCode weak (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some (some n) ↔ ∃ hn : 0 < n, ¬Holds weak a b ⟨n, hn⟩ ∧
        ∀ m : PosNat, (m : Nat) < n → Holds weak a b m

def SourceDecision : Prop :=
  ∀ (weak : Bool) (a b : Expr (Fin 1)),
    (decisionCode weak (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some true ↔ ∀ n : PosNat, Holds weak a b n) ∧
    (decisionCode weak (encodeExpr (a.rename Fin.val)) (encodeExpr (b.rename Fin.val)) =
      some false ↔ ¬∀ n : PosNat, Holds weak a b n)

def ActualUniformPrograms : Prop :=
  Primrec boundCode ∧
  Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => holdsAt p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Bool × (HeightCode × HeightCode) × Nat => firstFailure p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Bool × List Nat × List Nat => resultCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Bool × List Nat × List Nat => decisionCode p.1 p.2.1 p.2.2)

def Target : Prop := UnaryRayIdentity ∧ ExactFiniteScan ∧ ProvedEventualComparison ∧
  ExactRawDomain ∧ SourceResult ∧ SourceDecision ∧ ActualUniformPrograms

end LogicLineages.ComputabilityKnowledge.Comparators.UnaryComparison
