module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimaryEquivalence NumberedFiniteUniverse NumberedUniverseBindingTargets NumberedUniverseOperationsTargets NumberedUniverseOperationsProof NumberedWindowEquivalence NumberedWindowEquivalenceTargets

theorem actualPrimaryErasure : ActualPrimaryErasure := by
  intro Symbol arity symbols S Gamma q r h
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types a b _ => ArgumentPrimary Symbol arity Gamma types a b)
  case refl q => exact .refl q
  case symm h ih => exact .symm ih
  case trans h1 h2 ih1 ih2 => exact .trans ih1 ih2
  case ordinary f g base target hf hg he ht hp => exact .ordinary f g base target he ht hp
  case numbered k f g tau base target types extras hf hg he hp => exact .numbered k f g tau base target types extras he hp
  case lam q r h ih => exact .lam q r ih
  case appFunction q r a h ih => exact .appFunction q r a ih
  case appArgument q a b h ih => exact .appArgument q a b ih
  case ordinaryArguments f base target h ih => exact .ordinaryArguments f base target ih
  case numberedBase k f tau base target types extras h ih => exact .numberedBase k f tau base target types extras ih
  case numberedExtras k f tau base types extras target h ih => exact .numberedExtras k f tau base types extras target ih
  case nil => exact .nil
  case cons => exact .cons _ _ _ _ ‹Primary _ _ _ _ _› ‹ArgumentPrimary _ _ _ _ _ _›

theorem actualArgumentErasure : ActualArgumentErasure := by
  intro Symbol arity symbols S Gamma types a b h
  induction types with
  | nil => cases h; exact .nil
  | cons sigma types ih => cases h with
    | cons q r rest target hq ht =>
      exact .cons q r rest target (actualPrimaryErasure Symbol arity symbols S Gamma _ _ hq) (ih rest target ht)

theorem permutationGood {Symbol : Type} {arity : Symbol → Nat} (K : Ty → Prop) (H : Head Symbol → Prop)
    {Gamma xs ys : List Ty} (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (hp : (argumentList a).Perm (argumentList b)) : GoodArguments K H a ↔ GoodArguments K H b := by
  rw [actualArgumentOccurrences Symbol arity K H Gamma xs a,
      actualArgumentOccurrences Symbol arity K H Gamma ys b]
  constructor
  · intro h q hq; exact h q (hp.mem_iff.mpr hq)
  · intro h q hq; exact h q (hp.mem_iff.mp hq)

theorem actualPrimaryConfinement : ActualPrimaryConfinement := by
  intro Symbol arity symbols S Gamma q r h
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types a b _ =>
      GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) a ↔
      GoodArguments (fun t => t∈S) (HeadInWindow arity symbols S) b)
  case refl q => exact Iff.rfl
  case symm h ih => exact ih.symm
  case trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  case ordinary f g base target hf hg he ht hp =>
    have hb := permutationGood (fun t => t∈S) (HeadInWindow arity symbols S) base target hp
    constructor
    · intro h
      have hr := hb.mp ⟨h.1.2,h.2.2⟩
      exact ⟨⟨hg.2.1,hr.1⟩,hg,hr.2⟩
    · intro h
      have hr := hb.mpr ⟨h.1.2,h.2.2⟩
      exact ⟨⟨hf.2.1,hr.1⟩,hf,hr.2⟩
  case numbered k f g tau base target types extras hf hg he hp =>
    have hb := permutationGood (fun t => t∈S) (HeadInWindow arity symbols S) base target hp
    constructor
    · intro h
      have hr := hb.mp ⟨h.1.2.1,h.2.2.1⟩
      exact ⟨⟨h.1.1,hr.1,h.1.2.2⟩,hg,hr.2,h.2.2.2⟩
    · intro h
      have hr := hb.mpr ⟨h.1.2.1,h.2.2.1⟩
      exact ⟨⟨h.1.1,hr.1,h.1.2.2⟩,hf,hr.2,h.2.2.2⟩
  case lam q r h ih =>
    constructor
    · intro hq
      have hr := ih.mp ⟨hq.1.2.2,hq.2⟩
      exact ⟨⟨hq.1.1,hq.1.2.1,hr.1⟩,hr.2⟩
    · intro hr
      have hq := ih.mpr ⟨hr.1.2.2,hr.2⟩
      exact ⟨⟨hr.1.1,hr.1.2.1,hq.1⟩,hq.2⟩
  case appFunction q r a h ih =>
    constructor
    · intro hg
      have hr := ih.mp ⟨hg.1.2.1,hg.2.1⟩
      exact ⟨⟨hg.1.1,hr.1,hg.1.2.2⟩,hr.2,hg.2.2⟩
    · intro hg
      have hq := ih.mpr ⟨hg.1.2.1,hg.2.1⟩
      exact ⟨⟨hg.1.1,hq.1,hg.1.2.2⟩,hq.2,hg.2.2⟩
  case appArgument q a b h ih =>
    constructor
    · intro hg
      have hb := ih.mp ⟨hg.1.2.2,hg.2.2⟩
      exact ⟨⟨hg.1.1,hg.1.2.1,hb.1⟩,hg.2.1,hb.2⟩
    · intro hg
      have ha := ih.mpr ⟨hg.1.2.2,hg.2.2⟩
      exact ⟨⟨hg.1.1,hg.1.2.1,ha.1⟩,hg.2.1,ha.2⟩
  case ordinaryArguments f base target h ih =>
    constructor
    · intro hg
      have ht := ih.mp ⟨hg.1.2,hg.2.2⟩
      exact ⟨⟨hg.1.1,ht.1⟩,hg.2.1,ht.2⟩
    · intro hg
      have hb := ih.mpr ⟨hg.1.2,hg.2.2⟩
      exact ⟨⟨hg.1.1,hb.1⟩,hg.2.1,hb.2⟩
  case numberedBase k f tau base target types extras h ih =>
    constructor
    · intro hg
      have ht := ih.mp ⟨hg.1.2.1,hg.2.2.1⟩
      exact ⟨⟨hg.1.1,ht.1,hg.1.2.2⟩,hg.2.1,ht.2,hg.2.2.2⟩
    · intro hg
      have hb := ih.mpr ⟨hg.1.2.1,hg.2.2.1⟩
      exact ⟨⟨hg.1.1,hb.1,hg.1.2.2⟩,hg.2.1,hb.2,hg.2.2.2⟩
  case numberedExtras k f tau base types extras target h ih =>
    constructor
    · intro hg
      have ht := ih.mp ⟨hg.1.2.2,hg.2.2.2⟩
      exact ⟨⟨hg.1.1,hg.1.2.1,ht.1⟩,hg.2.1,hg.2.2.1,ht.2⟩
    · intro hg
      have he := ih.mpr ⟨hg.1.2.2,hg.2.2.2⟩
      exact ⟨⟨hg.1.1,hg.1.2.1,he.1⟩,hg.2.1,hg.2.2.1,he.2⟩
  case nil => exact Iff.rfl
  case cons Gamma sigma types q r rest target hq ht ihq iht =>
    constructor
    · intro hg
      have hr := ihq.mp ⟨hg.1.1,hg.2.1⟩
      have ht := iht.mp ⟨hg.1.2,hg.2.2⟩
      exact ⟨⟨hr.1,ht.1⟩,hr.2,ht.2⟩
    · intro hg
      have hq := ihq.mpr ⟨hg.1.1,hg.2.1⟩
      have ht := iht.mpr ⟨hg.1.2,hg.2.2⟩
      exact ⟨⟨hq.1,ht.1⟩,hq.2,ht.2⟩

theorem actualArgumentConfinement : ActualArgumentConfinement := by
  intro Symbol arity symbols S Gamma types a b h
  induction types with
  | nil => cases h; exact Iff.rfl
  | cons sigma types ih => cases h with
    | cons q r rest target hq ht =>
      have iq := actualPrimaryConfinement Symbol arity symbols S Gamma _ _ hq
      have it := ih rest target ht
      constructor
      · intro hg
        have hq := iq.mp ⟨hg.1.1,hg.2.1⟩
        have hr := it.mp ⟨hg.1.2,hg.2.2⟩
        exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩
      · intro hg
        have hq := iq.mpr ⟨hg.1.1,hg.2.1⟩
        have hr := it.mpr ⟨hg.1.2,hg.2.2⟩
        exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWindowEquivalenceProof
