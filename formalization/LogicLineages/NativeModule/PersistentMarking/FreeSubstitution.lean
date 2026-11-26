module

public import LogicLineages.NativeModule.PersistentMarking.SpineTyping

@[expose] public section

namespace LogicLineages.PersistentMarking.Spine

abbrev FreeMap := Ty → Nat → Expr

/- Image terms live in one outside bound context. Insertion beneath d retained
binders shifts their external indices, and never substitutes inside the image. -/
mutual
 def freeSub (θ : FreeMap) (d : Nat) : Expr → Expr
   | .free σ x => shift d 0 (θ σ x)
   | .bound σ i => .bound σ i
   | .lam σ body => .lam σ (freeSub θ (d+1) body)
   | .head f base => .head f (freeSubArgs θ d base)
   | .marked f τ base extras =>
       .marked f τ (freeSubArgs θ d base) (freeSubArgs θ d extras)
 def freeSubArgs (θ : FreeMap) (d : Nat) : Args → Args
   | .nil => .nil
   | .cons x xs => .cons (freeSub θ d x) (freeSubArgs θ d xs)
end

def FreeMapTyped (Γ : BoundContext) (θ : FreeMap) : Prop :=
  ∀ σ x, Typed Γ (θ σ x) σ

end LogicLineages.PersistentMarking.Spine
