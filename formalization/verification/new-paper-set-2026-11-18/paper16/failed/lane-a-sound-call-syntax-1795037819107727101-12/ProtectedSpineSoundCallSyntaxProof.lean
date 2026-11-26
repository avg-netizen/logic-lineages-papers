import LogicLineages.PersistentMarking.ProtectedSpineSoundFrameProof
import LogicLineages.PersistentMarking.BoundBlockProof
import LogicLineages.PersistentMarking.ClosedSyntaxProof

namespace LogicLineages.PersistentMarking.ProtectedSpineSoundCallSyntaxProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation

theorem ignoreTail (C : BoundContext) (q : Expr) (σ : Ty) (ht : Typed C q σ)
    (args prefix tail : Args) (hb : ClosedSyntaxProof.Bounded C prefix.length) :
    applyAux q args (prefix.append tail) = applyAux q args prefix := by
  have hSub := (ClosedSyntaxProof.term C prefix.length hb q σ ht 0 tail).2
  cases args with
  | nil =>
    have he := BoundBlockProof.block prefix tail 0 q
    simp only [Nat.zero_add,hSub] at he
    simpa only [applyAux] using congrArg some he.symm
  | cons a args =>
    cases q with
    | free => rfl
    | bound => rfl
    | lam δ body =>
      cases ht with
      | lam ht =>
        by_cases hA : a.type = δ
        · simp only [applyAux,hA,if_true]
          change applyAux body args ((.cons a prefix : Args).append tail) =
            applyAux body args (.cons a prefix)
          exact ignoreTail (C.push δ) body _ ht args (.cons a prefix) tail
            (by simpa [Args.length,Nat.add_comm] using ClosedSyntaxProof.pushBound hb δ)
        · simp [applyAux,hA]
    | head f bs =>
      cases ht with
      | head ht =>
        have he := BoundBlockProof.blockArgs prefix tail 0 bs
        have hBs := (ClosedSyntaxProof.bases C prefix.length hb bs f.arguments ht 0 tail).2
        simp only [Nat.zero_add,hBs] at he
        simp only [applyAux,he]
    | marked f τ bs es =>
      cases ht with
      | marked ht hs =>
        have he := BoundBlockProof.blockArgs prefix tail 0 bs
        have hBs := (ClosedSyntaxProof.bases C prefix.length hb bs f.arguments ht 0 tail).2
        have he' := BoundBlockProof.blockArgs prefix tail 0 es
        have hEs := (ClosedSyntaxProof.extras C prefix.length hb es hs 0 tail).2
        simp only [Nat.zero_add,hBs] at he
        simp only [Nat.zero_add,hEs] at he'
        simp only [applyAux,he,he']
termination_by sizeOf args

theorem closedAux (q : Expr) (σ : Ty) (ht : Typed EmptyContext q σ)
    (args prefix : Args) : applyAux q args prefix = apply q args := by
  have h := ignoreTail EmptyContext q σ ht args .nil prefix ClosedSyntaxProof.emptyBound
  cases args with
  | nil => exact congrArg some (ClosedSyntaxProof.closedSubstitute q σ ht prefix)
  | cons => exact h

theorem openCombined (values : Args) (σ : Ty) (x : Nat) (body : Expr) :
    openBody σ x (substitute values 1 body) = substitute (.cons (.free σ x) values) 0 body := by
  exact BoundBlockProof.block (.cons (.free σ x) .nil) values 0 body

theorem emptyCombined (prefix outer : Args) (body : Expr) :
    applyAux (substitute outer prefix.length body) .nil prefix =
      some (substitute (prefix.append outer) 0 body) := by
  have h := BoundBlockProof.block prefix outer 0 body
  simpa only [applyAux,Nat.zero_add] using congrArg some h

theorem arrowPrefix {α β d τ : Ty} {ds : List Ty}
    (hp : (d::ds,τ) ∈ fullPrefixes (.arrow α β)) :
    d=α ∧ (ds=[] ∧ τ=β ∨ (ds,τ) ∈ fullPrefixes β) := by
  have h := Ty.arrow.inj (FinitePrefixProof.forward _ _ _ hp).2
  refine ⟨h.1,?_⟩
  cases ds with
  | nil => exact Or.inl ⟨rfl,h.2⟩
  | cons d ds =>
    exact Or.inr ((FinitePrefixProof.exactPrefix _ _ _).mpr ⟨by simp,h.2⟩)

end LogicLineages.PersistentMarking.ProtectedSpineSoundCallSyntaxProof
