module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesRelationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison ComparisonFreeVariables ComparisonFreeVariablesSyntaxProof ComparisonFreeVariablesApplicationProof

abbrev ListSupported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (ss : List (Packed Symbol arity Γ)) (a : Allowed Γ) := ∀ p ∈ ss,Supported p.2 a

private theorem selfSupported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types) (requested : List Ty) (a : Allowed Γ)
    (h : ArgumentsSupported base a ∧ ArgumentsSupported extras a) :
    ArgumentsSupported (selfArguments f base types extras requested) a := by
  induction requested with
  | nil => trivial
  | cons σ rest ih => exact ⟨h,ih⟩

private theorem openSupported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (f : Head Symbol) (σ τ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (types : List Ty) (extras : Arguments Symbol arity Γ types) (a : Allowed Γ)
    (h : ArgumentsSupported base a ∧ ArgumentsSupported extras a) : Supported (openMarked f σ τ base types extras) (liftAllowed a) := by
  constructor
  · exact renameArgumentsSupported base a (liftAllowed a) (Renaming.weaken Γ σ) h.1 (by intros; assumption)
  · apply (appendSupported _ _ (liftAllowed a)).mpr
    exact ⟨renameArgumentsSupported extras a (liftAllowed a) (Renaming.weaken Γ σ) h.2 (by intros; assumption),⟨trivial,trivial⟩⟩

theorem weakSupported {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Γ : List Ty} {s t : Packed Symbol arity Γ} (h : Weak Symbol arity above Γ s t) :
    ∀ a : Allowed Γ, Supported s.2 a → Supported t.2 a := by
  induction h using Weak.rec
    (motive_2 := fun Γ s t _ => ∀ a : Allowed Γ,Supported s.2 a → Supported t.2 a)
    (motive_3 := fun Γ ss ts _ => ∀ a : Allowed Γ,ListSupported ss a → ListSupported ts a)
    (motive_4 := fun Γ ss ts _ => ∀ a : Allowed Γ,ListSupported ss a → ListSupported ts a)
    (motive_5 := fun Γ ss ts _ => ∀ a : Allowed Γ,ListSupported ss a → ListSupported ts a)
  case var v => intro a hs; exact hs
  case abs s t hw ih => intro a hs; exact ih (liftAllowed a) hs
  case fun_ f g ss ts matched he ht hp hm ih =>
      intro a hs
      apply (argumentsListSupported ts a).mpr
      have hout := ih a ((argumentsListSupported ss a).mp hs)
      intro p hmem
      exact hout p (hp.mem_iff.mp hmem)
  case put f ss t hw ih => intro a hs; exact ih a ⟨hs,trivial⟩
  case select f ss types extras requested q r t suffix hmem happ hw ih =>
      intro a hs
      apply ih a
      apply originalApplyProvenance _ _ _ _ _ _ requested q (fun v => .var v)
        (selfArguments f ss types extras requested) suffix r a a
      · rcases List.mem_append.mp hmem with hb | he
        · exact (argumentsListSupported ss a).mp hs.1 _ hb
        · exact (argumentsListSupported extras a).mp hs.2 _ he
      · intro υ v hv; exact hv
      · exact selfSupported f ss types extras requested a hs
      · exact happ
  case fAbs f ss types extras t hw ih =>
      intro a hs
      exact ih (liftAllowed a) (openSupported f _ _ ss types extras a hs)
  case copy f g ss types extras ts ha hw ih =>
      intro a hs
      apply (argumentsListSupported ts a).mpr
      intro p hp
      exact ih p hp a hs
  case stat f g ss types extras ts he hm hw ihm ihw =>
      intro a hs
      apply (argumentsListSupported ts a).mpr
      intro p hp
      exact ihw p hp a hs
  case mark s r t hm hw ih a hs =>
      exact ih a (markSupported s r hm a hs)
  case nil => intro p hp; cases hp
  case cons s t ss ts hw hm ihw ihm a hs =>
      intro p hp
      rcases List.mem_cons.mp hp with he | ht
      · subst p; exact ihw a (hs s List.mem_cons_self)
      · exact ihm a (fun q hq => hs q (List.mem_cons_of_mem s hq)) p ht
  case replace ss ts kept retained removed inserted hp hq hn hw hr ihw ihr a hs =>
      intro p hmem
      have hk : ListSupported kept a := fun q hq => hs q (hp.mem_iff.mpr (List.mem_append.mpr (Or.inl hq)))
      have hd : ListSupported removed a := fun q hq => hs q (hp.mem_iff.mpr (List.mem_append.mpr (Or.inr hq)))
      rcases List.mem_append.mp (hq.mem_iff.mp hmem) with hk' | hi
      · exact ihw a hk p hk'
      · exact ihr a hd p hi
  case nil => intro hs p hp; cases hp
  case cons removed s t rest hs hst hr ihst ihr a =>
      intro ha p hp
      rcases List.mem_cons.mp hp with he | ht
      · subst p; exact ihst a (ha s hs)
      · exact ihr a ha p ht

theorem strictSupported {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Γ : List Ty} {s t : Packed Symbol arity Γ} (h : Strict Symbol arity above Γ s t)
    (a : Allowed Γ) (hs : Supported s.2 a) : Supported t.2 a := by
  cases h with
  | mark s r t hm hw => exact weakSupported hw a (markSupported s r hm a hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesRelationProof
