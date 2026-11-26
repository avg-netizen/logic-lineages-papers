import LogicLineages.PersistentMarking.NativeReduction
namespace LogicLineages.PersistentMarking.NativeOrientationTargets
open Spine NativeReduction

def FirstFullCall : Prop := ∀ τ n A B,
  apply (rec2 τ (succ n) A) (.cons (P τ n A B τ) .nil) = some (C2 τ n A B τ)
def SecondFullCall : Prop := ∀ τ n A B,
  apply (rec1 τ (succ n)) (.cons (C2 τ n A B (stepType τ)) (.cons (C2 τ n A B τ) .nil)) = some (C1 τ n A B τ)
def ThirdFullCall : Prop := ∀ τ n A B,
  apply (.head (.recursor τ) .nil)
    (.cons (C1 τ n A B .ground) (.cons (C1 τ n A B (stepType τ)) (.cons (C1 τ n A B τ) .nil))) = some (C0 τ n A B τ)

def Beta : Prop := ∀ S σ τ body B,
  Typed (EmptyContext.push σ) body τ → Valid S body → Ordinary body → PaperTerm S B σ → Ordinary B →
  ConfinedPair.Strict S (app σ τ (.lam σ body) B) (substitute (.cons B .nil) 0 body)
def CaseZero : Prop := ∀ S τ A B, PaperTerm S A τ → Ordinary A → PaperTerm S B τ → Ordinary B →
  ConfinedPair.Strict S (caseTerm τ zero A B) A
def CaseSucc : Prop := ∀ S τ n A B, PaperTerm S n .ground → Ordinary n →
  PaperTerm S A τ → Ordinary A → PaperTerm S B τ → Ordinary B →
  ConfinedPair.Strict S (caseTerm τ (succ n) A B) B
def RecZero : Prop := ∀ S τ A B, PaperTerm S A (stepType τ) → Ordinary A → PaperTerm S B τ → Ordinary B →
  ConfinedPair.Strict S (recTerm τ zero A B) B
def RecSucc : Prop := ∀ S τ n A B, PaperTerm S n .ground → Ordinary n →
  PaperTerm S A (stepType τ) → Ordinary A → PaperTerm S B τ → Ordinary B →
  ConfinedPair.Strict S (recTerm τ (succ n) A B) (app τ τ (app .ground (.arrow τ τ) A n) (recTerm τ n A B))

def PrimitiveOrientation : Prop := ∀ S s t, Primitive S s t → ConfinedPair.Strict S s t
def FullOrientation : Prop := ∀ S s t, Reduction S s t → ConfinedPair.Strict S s t
end LogicLineages.PersistentMarking.NativeOrientationTargets
