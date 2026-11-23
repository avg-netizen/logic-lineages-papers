module

public import LogicLineages.NativeModule.PersistentMarking.RefinementSubstitutionSupport
public import LogicLineages.NativeModule.PersistentMarking.RefinementFreshOpeningProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementSubstitutionProof
open Spine NameBridge RefinementMeasure RefinementSubstitutionSupport OpeningFoundationProof

def Related (S : Signature) (γ δ : FreeMap) : Prop := ∀ σ x, Refines S (γ σ x) (δ σ x)

def Smaller (S : Signature) (n : Nat) : Prop := ∀ {q s : Expr} (h : RefinementTree S q s),
  treeSize h < n → ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
  Refines S (freeSub γ 0 q) (freeSub δ 0 s)

theorem mappedAt (θ : FreeMap) {qs i q} (h : At qs i q) : At (freeSubArgs θ 0 qs) i (freeSub θ 0 q) := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem bases (S : Signature) (n : Nat) (ih : Smaller S n) (qs ss : Args)
    (h : RefinementBasesTree S qs ss) (hb : basesSize h < n) (γ δ : FreeMap)
    (hg : FreeMapTyped EmptyContext γ) (hd : FreeMapTyped EmptyContext δ) (he : Related S γ δ) :
    _root_.Nonempty (RefinementBasesTree S (freeSubArgs γ 0 qs) (freeSubArgs δ 0 ss)) := by
  cases h with
  | nil => exact ⟨.nil⟩
  | cons r rs =>
    have hr : treeSize r < n := by change 1 + treeSize r + basesSize rs < n at hb; omega
    have hrs : basesSize rs < n := by change 1 + treeSize r + basesSize rs < n at hb; omega
    obtain ⟨out⟩ := ih r hr γ δ hg hd he
    obtain ⟨outs⟩ := bases S n ih _ _ rs hrs γ δ hg hd he
    exact ⟨.cons out outs⟩
termination_by sizeOf ss

theorem extra (S : Signature) (n : Nat) (ih : Smaller S n) (f : Head) (base es : Args) (s : Expr)
    (h : RefinementExtraTree S f base es s) (hb : extraSize h < n) (γ δ : FreeMap)
    (hg : FreeMapTyped EmptyContext γ) (hd : FreeMapTyped EmptyContext δ) (he : Related S γ δ) :
    _root_.Nonempty (RefinementExtraTree S f (freeSubArgs γ 0 base) (freeSubArgs γ 0 es) (freeSub δ 0 s)) := by
  cases h with
  | existing ha r =>
    have hr : treeSize r < n := by change 1 + treeSize r < n at hb; omega
    obtain ⟨out⟩ := ih r hr γ δ hg hd he
    exact ⟨.existing (mappedAt γ ha) out⟩
  | owner r =>
    have hr : treeSize r < n := by change 1 + treeSize r < n at hb; omega
    obtain ⟨out⟩ := ih r hr γ δ hg hd he
    have ht := FreeCallProof.annotation δ (fun τ x => SpineShiftProof.annotationExact _ _ _ (hd τ x)) 0 s
    have ht' : freeSub γ 0 (.marked f s.type base es) = .marked f (freeSub δ 0 s).type (freeSubArgs γ 0 base) (freeSubArgs γ 0 es) := by
      simp only [freeSub,ht]
    obtain ⟨out',_⟩ := RefinementRenamingProof.transport ht' rfl out
    exact ⟨.owner out'⟩

theorem extras (S : Signature) (n : Nat) (ih : Smaller S n) (f : Head) (base es ss : Args)
    (h : RefinementExtrasTree S f base es ss) (hb : extrasSize h < n) (γ δ : FreeMap)
    (hg : FreeMapTyped EmptyContext γ) (hd : FreeMapTyped EmptyContext δ) (he : Related S γ δ) :
    _root_.Nonempty (RefinementExtrasTree S f (freeSubArgs γ 0 base) (freeSubArgs γ 0 es) (freeSubArgs δ 0 ss)) := by
  cases h with
  | nil => exact ⟨.nil⟩
  | cons r rs =>
    have hr : extraSize r < n := by change 1 + extraSize r + extrasSize rs < n at hb; omega
    have hrs : extrasSize rs < n := by change 1 + extraSize r + extrasSize rs < n at hb; omega
    obtain ⟨out⟩ := extra S n ih f base es _ r hr γ δ hg hd he
    obtain ⟨outs⟩ := extras S n ih f base es _ rs hrs γ δ hg hd he
    exact ⟨.cons out outs⟩
termination_by sizeOf ss

theorem tree (S : Signature) (n : Nat) : ∀ q s (h : RefinementTree S q s), treeSize h = n →
    ∀ γ δ, FreeMapTyped EmptyContext γ → FreeMapTyped EmptyContext δ → Related S γ δ →
    Refines S (freeSub γ 0 q) (freeSub δ 0 s) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro q s h hn γ δ hg hd he
    have smaller : Smaller S n := by
      intro q s r hr γ δ hg hd he
      exact ih (treeSize r) hr q s r rfl γ δ hg hd he
    have hvg : ∀ τ x, Valid S (γ τ x) := by
      intro τ x
      obtain ⟨h⟩ := he τ x
      exact (endpoints h).1.2
    have hvd : ∀ τ x, Valid S (δ τ x) := by
      intro τ x
      obtain ⟨h⟩ := he τ x
      exact (endpoints h).2.2
    cases h with
    | @var σ x =>
      simpa only [freeSub,SubstitutionProof.shiftZero] using he σ x
    | @head f qs ss hp hs hb =>
      have hb' : basesSize hb < n := by change 1 + basesSize hb = n at hn; omega
      obtain ⟨out⟩ := bases S n smaller qs ss hb hb' γ δ hg hd he
      exact ⟨.head (subPaper S γ hg hvg _ _ hp) (subPaper S δ hd hvd _ _ hs) out⟩
    | @marked f τ qb qe sb se hp hs hb hex =>
      have hb' : basesSize hb < n := by change 1 + basesSize hb + extrasSize hex = n at hn; omega
      have he' : extrasSize hex < n := by change 1 + basesSize hb + extrasSize hex = n at hn; omega
      obtain ⟨outb⟩ := bases S n smaller qb sb hb hb' γ δ hg hd he
      obtain ⟨oute⟩ := extras S n smaller f qb qe se hex he' γ δ hg hd he
      exact ⟨.marked (subPaper S γ hg hvg _ _ hp) (subPaper S δ hd hvd _ _ hs) outb oute⟩
    | @abs σ q τ s x hp hs hxq hxs hc =>
      let z := max (maxFreeName q) (max (maxFreeName s) (max (imageBound γ q) (imageBound δ s))) + 1
      have hzq : freeOccurs (σ,z) q = false := aboveFresh σ z q (by dsimp [z]; omega)
      have hzs : freeOccurs (σ,z) s = false := aboveFresh σ z s (by dsimp [z]; omega)
      have hzg : freeOccurs (σ,z) (freeSub γ 1 q) = false := imageFresh γ σ z 1 q (by dsimp [z]; omega)
      have hzd : freeOccurs (σ,z) (freeSub δ 1 s) = false := imageFresh δ σ z 1 s (by dsimp [z]; omega)
      obtain ⟨hc',hce⟩ := RefinementOpeningProof.synchronize S σ x z q s hxq hxs hzq hzs hc
      have hr : treeSize hc' < n := by change 1 + treeSize hc = n at hn; omega
      obtain ⟨out⟩ := smaller hc' hr (mask γ σ z) (mask δ σ z) (maskTyped γ σ z hg) (maskTyped δ σ z hd) (maskRefines S γ δ σ z he)
      obtain ⟨out',_⟩ := RefinementRenamingProof.transport (maskedOpening γ σ z q hzq) (maskedOpening δ σ z s hzs) out
      exact ⟨.abs (subPaper S γ hg hvg _ _ hp) (subPaper S δ hd hvd _ _ hs) hzg hzd out'⟩

theorem freeSubstitution : RefinementSyntaxTargets.FreeSubstitution := by
  intro S γ δ q s hg hd he h
  obtain ⟨h⟩ := h
  exact tree S (treeSize h) q s h rfl γ δ hg hd he

theorem arbitraryRenaming : RefinementSyntaxTargets.Renaming := by
  intro S π q s h
  exact freeSubstitution S (fun σ x => .free σ (π σ x)) (fun σ x => .free σ (π σ x)) q s
    (fun _ _ => .free) (fun _ _ => .free) (fun _ _ => ⟨.var⟩) h
end LogicLineages.PersistentMarking.RefinementSubstitutionProof
