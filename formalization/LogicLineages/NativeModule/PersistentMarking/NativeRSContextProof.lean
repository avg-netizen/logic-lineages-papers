module

public import LogicLineages.NativeModule.PersistentMarking.NativeRSFamiliesProof
public import LogicLineages.NativeModule.PersistentMarking.StablePairProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NativeRSContextProof
open Spine StructuralContext NativeReduction NativeTypingProof NativeRSFamiliesProof

theorem succStrict (S : Signature) (n : Expr) (hn : PaperTerm S n .ground) (ho : Ordinary n) :
    ConfinedPair.Strict S (succ n) n := by
  have hs := succPaper S n hn
  exact ⟨⟨.ground,hs,hn,⟨True.intro,ho,True.intro⟩,ho⟩,
    Strict.intro hs hn rfl (secondSelect S .ground .ground _ n .nil (succConstantPaper S) hn ho .nil True.intro),
    rightIncluded .ground .ground _ n⟩

def recContext (τ : Ty) (A B : Expr) : Context :=
  .head (.app τ τ) .nil
    (.head (.app (stepType τ) (.arrow τ τ)) .nil
      (.head (.app .ground (.arrow (stepType τ) (.arrow τ τ))) (.cons (.head (.recursor τ) .nil) .nil) .hole .nil)
      (.cons A .nil)) (.cons B .nil)

theorem recContextTyped (S : Signature) (τ : Ty) (A B : Expr)
    (hA : PaperTerm S A (stepType τ)) (hoA : Ordinary A) (hB : PaperTerm S B τ) (hoB : Ordinary B) :
    ContextTyped S (recContext τ A B) .ground τ := by
  have hc1 : ContextTyped S
      (.head (.app .ground (.arrow (stepType τ) (.arrow τ τ))) (.cons (.head (.recursor τ) .nil) .nil) .hole .nil)
      .ground (.arrow (stepType τ) (.arrow τ τ)) :=
    .head .hole ⟨0,rfl⟩ (.cons (recConstantPaper S τ).1 .nil) ⟨(recConstantPaper S τ).2,True.intro⟩
      ⟨True.intro,True.intro⟩ .nil True.intro True.intro rfl
  exact .head (.head hc1 ⟨0,rfl⟩ .nil True.intro True.intro (.cons hA.1 .nil)
      ⟨hA.2,True.intro⟩ ⟨hoA,True.intro⟩ rfl) ⟨0,rfl⟩ .nil True.intro True.intro
      (.cons hB.1 .nil) ⟨hB.2,True.intro⟩ ⟨hoB,True.intro⟩ rfl

theorem recPredecessor (S : Signature) (τ : Ty) (n A B : Expr)
    (hn : PaperTerm S n .ground) (hon : Ordinary n) (hA : PaperTerm S A (stepType τ)) (hoA : Ordinary A)
    (hB : PaperTerm S B τ) (hoB : Ordinary B) :
    ConfinedPair.Strict S (recTerm τ (succ n) A B) (recTerm τ n A B) := by
  exact StablePairProof.strictContext S (recContext τ A B) .ground τ (succ n) n
    (recContextTyped S τ A B hA hoA hB hoB) (succPaper S n hn) hn (succStrict S n hn hon)

theorem predecessorWeak (S : Signature) (τ : Ty) (n A B : Expr)
    (hn : PaperTerm S n .ground) (hon : Ordinary n) (hA : PaperTerm S A (stepType τ)) (hoA : Ordinary A)
    (hB : PaperTerm S B τ) (hoB : Ordinary B) :
    Weak S (P τ n A B τ) (recTerm τ n A B) := by
  have hh := (recPredecessor S τ n A B hn hon hA hoA hB hoB).2.1
  cases hh with
  | @intro q σ t r hp ht hm hw =>
    have he : P τ n A B τ = r := Option.some.inj hm
    subst r
    exact hw
end LogicLineages.PersistentMarking.NativeRSContextProof
