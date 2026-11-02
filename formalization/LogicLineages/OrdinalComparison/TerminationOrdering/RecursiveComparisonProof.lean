module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonProof
open Source Source.SourceMarkedSyntax RecursiveComparison

theorem weakTypeSoundness : RecursiveComparisonTargets.WeakTypeSoundness := by
  intro Symbol arity above Γ s t h
  cases h <;> first | rfl | assumption

theorem strictTypeSoundness : RecursiveComparisonTargets.StrictTypeSoundness := by
  intro Symbol arity above Γ s t h
  cases h
  rfl

theorem markedStrictEmpty : RecursiveComparisonTargets.MarkedStrictEmpty := by
  intro Symbol arity above Γ f τ base types extras t h
  cases h with
  | mark s r t hm hw => cases hm

theorem strictMarkHelperAgreement : RecursiveComparisonTargets.StrictMarkHelperAgreement := by
  intro Symbol arity Γ τ s
  induction s using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro r hm; cases hm
  | lam body ih =>
      intro r he
      simp only [strictMark] at he
      cases hm : strictMark body with
      | none => simp [hm] at he
      | some out =>
          simp only [hm,Option.map_some,Option.some.injEq] at he
          subst r
          simp only [markSpine,ih out hm,Option.map_some]
  | ordinary hd base ih => intro r he; exact he
  | marked hd output base extraTypes extras ihb ihe => intro r he; cases he
  | nil => trivial
  | cons q rest ihq ihr => trivial

private def packedShape {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (p : Packed Symbol arity Γ) : Nat :=
  match p with
  | ⟨_,.var _⟩ => 0
  | ⟨_,.lam _⟩ => 1
  | ⟨_,.ordinary _ _⟩ => 2
  | ⟨_,.marked _ _ _ _ _⟩ => 3

private theorem unmarkWeak {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (above : Symbol → Symbol → Prop) (s : MarkedTerm Symbol arity Γ τ) :
    ∀ (r t : MarkedTerm Symbol arity Γ τ), strictMark s=some r →
      Weak Symbol arity above Γ ⟨τ,r⟩ ⟨τ,t⟩ → Weak Symbol arity above Γ ⟨τ,s⟩ ⟨τ,t⟩ := by
  induction s using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro r t hm hw; cases hm
  | lam body ih =>
      intro r t he hw
      simp only [strictMark] at he
      cases hm : strictMark body with
      | none => simp [hm] at he
      | some out =>
          simp only [hm,Option.map_some,Option.some.injEq] at he
          subst r
          generalize hs : (⟨_,.lam out⟩ : Packed Symbol arity _) = ps at hw
          generalize ht : (⟨_,t⟩ : Packed Symbol arity _) = pt at hw
          cases hw <;> try { have hn := congrArg packedShape hs; cases hn }
          case abs a b hb =>
            cases hs
            cases ht
            exact .abs body b (ih out b hm hb)
  | ordinary hd base ih =>
      intro r t he hw
      have hr : .marked hd (headResult hd) base [] .nil=r := Option.some.inj he
      subst r
      exact .put hd base t hw
  | marked hd output base extraTypes extras ihb ihe => intro r t he hw; cases he
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem strictWeakInclusion : RecursiveComparisonTargets.StrictWeakInclusion := by
  intro Symbol arity above Γ s t h
  cases h with
  | mark s r t hm hw => exact unmarkWeak above s r t hm hw

private theorem groundMatch {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) {Γ : List Ty} (n : Nat)
    (f : Fin n → MarkedTerm Symbol arity Γ .ground)
    (h : ∀ i,Weak Symbol arity above Γ ⟨.ground,f i⟩ ⟨.ground,f i⟩) :
    WeakMatch Symbol arity above Γ (argumentList (groundArguments n f)) (argumentList (groundArguments n f)) := by
  induction n with
  | zero => exact .nil
  | succ n ih =>
      exact .cons _ _ _ _ (h 0) (ih (fun i => f i.succ) (fun i => h i.succ))

theorem literalOrdinaryReflexivity : RecursiveComparisonTargets.LiteralOrdinaryReflexivity := by
  intro Symbol arity above Γ τ s
  induction s with
  | var v => exact .var v
  | app f a ihf iha =>
      apply Weak.fun_ (.application _ _) (.application _ _)
        (.cons (embed f) (.cons (embed a) .nil)) (.cons (embed f) (.cons (embed a) .nil)) _ rfl rfl (.refl _)
      exact .cons _ _ _ _ ihf (.cons _ _ _ _ iha .nil)
  | lam body ih => exact .abs _ _ ih
  | zeroC => exact .fun_ .zero .zero .nil .nil [] rfl rfl (.refl _) .nil
  | succC => exact .fun_ .succ .succ .nil .nil [] rfl rfl (.refl _) .nil
  | caseC τ => exact .fun_ (.cases τ) (.cases τ) .nil .nil [] rfl rfl (.refl _) .nil
  | recC τ => exact .fun_ (.recursor τ) (.recursor τ) .nil .nil [] rfl rfl (.refl _) .nil
  | ranked hd args ih =>
      exact .fun_ (.ranked hd) (.ranked hd)
        (groundArguments (arity hd) (fun i => embed (args i)))
        (groundArguments (arity hd) (fun i => embed (args i))) _ rfl rfl (.refl _)
        (groundMatch above (arity hd) (fun i => embed (args i)) ih)

end LogicLineages.OrdinalComparison.TerminationOrdering.RecursiveComparisonProof
