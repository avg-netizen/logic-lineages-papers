module

public import LogicLineages.NativeModule.PersistentMarking.StablePairTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeReduction
open Spine StructuralContext

def app (σ τ : Ty) (f a : Expr) : Expr := .head (.app σ τ) (.cons f (.cons a .nil))
def zero : Expr := .head .zero .nil
def succ (n : Expr) : Expr := app .ground .ground (.head .succ .nil) n
def stepType (τ : Ty) : Ty := .arrow .ground (.arrow τ τ)
def caseTerm (τ : Ty) (u A B : Expr) : Expr :=
  app τ τ (app τ (.arrow τ τ) (app .ground (.arrow τ (.arrow τ τ)) (.head (.case τ) .nil) u) A) B
def rec1 (τ : Ty) (u : Expr) : Expr :=
  app .ground (.arrow (stepType τ) (.arrow τ τ)) (.head (.recursor τ) .nil) u
def rec2 (τ : Ty) (u A : Expr) : Expr := app (stepType τ) (.arrow τ τ) (rec1 τ u) A
def recTerm (τ : Ty) (u A B : Expr) : Expr := app τ τ (rec2 τ u A) B

def P (τ : Ty) (n A B : Expr) (ρ : Ty) : Expr :=
  .marked (.app τ τ) ρ (.cons (rec2 τ (succ n) A) (.cons B .nil)) .nil
def C2 (τ : Ty) (n A B : Expr) (ρ : Ty) : Expr :=
  .marked (.app (stepType τ) (.arrow τ τ)) ρ (.cons (rec1 τ (succ n)) (.cons A .nil))
    (.cons (P τ n A B τ) .nil)
def C1 (τ : Ty) (n A B : Expr) (ρ : Ty) : Expr :=
  .marked (.app .ground (.arrow (stepType τ) (.arrow τ τ))) ρ
    (.cons (.head (.recursor τ) .nil) (.cons (succ n) .nil))
    (.cons (C2 τ n A B (stepType τ)) (.cons (C2 τ n A B τ) .nil))
def C0 (τ : Ty) (n A B : Expr) (ρ : Ty) : Expr :=
  .marked (.recursor τ) ρ .nil
    (.cons (C1 τ n A B .ground) (.cons (C1 τ n A B (stepType τ)) (.cons (C1 τ n A B τ) .nil)))

inductive Primitive (S : Signature) : Expr → Expr → Prop where
  | beta : Typed (EmptyContext.push σ) body τ → Valid S body → Ordinary body →
      PaperTerm S B σ → Ordinary B →
      Primitive S (app σ τ (.lam σ body) B) (substitute (.cons B .nil) 0 body)
  | caseZero : PaperTerm S A τ → Ordinary A → PaperTerm S B τ → Ordinary B →
      Primitive S (caseTerm τ zero A B) A
  | caseSucc : PaperTerm S n .ground → Ordinary n → PaperTerm S A τ → Ordinary A →
      PaperTerm S B τ → Ordinary B → Primitive S (caseTerm τ (succ n) A B) B
  | recZero : PaperTerm S A (stepType τ) → Ordinary A → PaperTerm S B τ → Ordinary B →
      Primitive S (recTerm τ zero A B) B
  | recSucc : PaperTerm S n .ground → Ordinary n → PaperTerm S A (stepType τ) → Ordinary A →
      PaperTerm S B τ → Ordinary B →
      Primitive S (recTerm τ (succ n) A B) (app τ τ (app .ground (.arrow τ τ) A n) (recTerm τ n A B))

/- Actual one-step instances closed under original well-typed contexts and
ordinary capture-avoiding substitutions, not transitive reduction closure. -/
inductive Reduction (S : Signature) : Expr → Expr → Prop where
  | primitive : Primitive S s t → Reduction S s t
  | context : ContextTyped S C σ τ → PaperTerm S s σ → PaperTerm S t σ → Reduction S s t →
      Reduction S (fill C s) (fill C t)
  | substitution : StructuralStabilityTargets.OrdinaryMap S θ → Reduction S s t →
      Reduction S (freeSub θ 0 s) (freeSub θ 0 t)
end LogicLineages.PersistentMarking.NativeReduction
