import LogicLineages.PersistentMarking.TwoEnvironmentBinderProof
namespace LogicLineages.PersistentMarking.TwoEnvironmentCases
open Spine NameBridge TwoEnvironmentSupport RefinementSubstitutionSupport ExtendedMeasure

theorem case_var (S : Signature) (n : Nat) (small : Smaller S n)
    (hn : 1 = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.free σ x) (.free σ x)) := by
  intro γ δ hg hd he
  simpa only [Result,freeSub,SubstitutionProof.shiftZero] using he _ _

theorem case_abs (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.lam σ s) (.arrow σ τ))
    (ht : PaperTerm S (.lam σ t) (.arrow σ τ))
    (hxs : freeOccurs (σ,x) s = false)
    (hxt : freeOccurs (σ,x) t = false)
    (hc : ExtendedTree S (.weak (openBody σ x s) (openBody σ x t)))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.lam σ s) (.lam σ t)) := by
  intro γ δ hg hd he
  exact TwoEnvironmentBinderProof.abstraction S n small σ τ s t x hp ht hxs hxt hc (by omega) γ δ hg hd he

theorem case_funHead (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S (.head g ts) g.result)
    (heq : Equivalent S f g)
    (htype : f.result = g.result)
    (hm : ExtendedTree S (.matching ss ts))
    (hn : 1 + treeSize hm = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.head f ss) (.head g ts)) := by
  intro γ δ hg hd he
  obtain ⟨hm'⟩ := small _ hm (by omega) γ δ hg hd he
  exact ⟨.funHead (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) heq htype hm'⟩

theorem case_put (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.head f ss) f.result)
    (ht : PaperTerm S t f.result)
    (hc : ExtendedTree S (.weak (.marked f f.result ss .nil) t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.head f ss) t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  exact ⟨.put (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) hc'⟩

theorem case_select (S : Signature) (n : Nat) (small : Smaller S n)
    (hp : PaperTerm S (.marked f τ ss es) τ)
    (ht : PaperTerm S t τ)
    (ha : (At ss i q ∨ At es i q))
    (hq : Typed EmptyContext q (ArrowPrefix domains τ))
    (hcall : apply q (ownerCopies f ss es domains) = some r)
    (hc : ExtendedTree S (.weak r t))
    (hn : 1 + treeSize hc = n) : ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ → Result S γ δ (.weak (.marked f τ ss es) t) := by
  intro γ δ hg hd he
  obtain ⟨hc'⟩ := small _ hc (by omega) γ δ hg hd he
  have hat := ha.elim (fun h => Or.inl (mappedAt γ h)) (fun h => Or.inr (mappedAt γ h))
  have hq' := FreeTypingProof.freeSubTyped EmptyContext γ hg q (ArrowPrefix domains τ) hq
  have hcall' := TwoEnvironmentSupport.call γ hg hcall
  rw [TwoEnvironmentSupport.ownerCopies] at hcall'
  exact ⟨.select (subPaper S γ hg (leftValid he) _ _ hp) (subPaper S δ hd (rightValid he) _ _ ht) hat hq' hcall' hc'⟩
end LogicLineages.PersistentMarking.TwoEnvironmentCases
