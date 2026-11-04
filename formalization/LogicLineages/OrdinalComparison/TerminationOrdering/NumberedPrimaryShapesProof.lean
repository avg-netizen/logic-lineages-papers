module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedPrimaryShapes

theorem actualPrimaryLambdaShape : NumberedPrimaryShapesTargets.ActualPrimaryLambdaShape := by
  intro Symbol arity symbols S Gamma q r h
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  all_goals first | rfl | trivial

def appView {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Option (Packed Symbol arity Gamma × Packed Symbol arity Gamma) :=
  match q.2 with
  | .app f a => some (⟨_,f⟩,⟨_,a⟩)
  | _ => none

inductive ViewRelated {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S Gamma : List Ty) :
    Option (Packed Symbol arity Gamma × Packed Symbol arity Gamma) →
    Option (Packed Symbol arity Gamma × Packed Symbol arity Gamma) → Prop where
  | none : ViewRelated symbols S Gamma none none
  | some (f a g b : Packed Symbol arity Gamma) : WindowPrimary Symbol arity symbols S Gamma f g →
      WindowPrimary Symbol arity symbols S Gamma a b → ViewRelated symbols S Gamma (some (f,a)) (some (g,b))

theorem viewRefl {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    (v : Option (Packed Symbol arity Gamma × Packed Symbol arity Gamma)) : ViewRelated symbols S Gamma v v := by
  cases v with
  | none => exact .none
  | some p => exact .some p.1 p.2 p.1 p.2 (.refl _) (.refl _)

theorem viewSymm {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {x y : Option (Packed Symbol arity Gamma × Packed Symbol arity Gamma)} (h : ViewRelated symbols S Gamma x y) :
    ViewRelated symbols S Gamma y x := by
  cases h with
  | none => exact .none
  | some f a g b hf ha => exact .some g b f a (.symm hf) (.symm ha)

theorem viewTrans {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {x y z : Option (Packed Symbol arity Gamma × Packed Symbol arity Gamma)}
    (h : ViewRelated symbols S Gamma x y) (k : ViewRelated symbols S Gamma y z) : ViewRelated symbols S Gamma x z := by
  cases h with
  | none => cases k; exact .none
  | some f a g b hf ha => cases k with
    | some _ _ j c hg hb => exact .some f a j c (.trans hf hg) (.trans ha hb)

theorem primaryAppView {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    ViewRelated symbols S Gamma (appView q) (appView r) := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl q => exact viewRefl _
  case symm h ih => exact viewSymm ih
  case trans h1 h2 ih1 ih2 => exact viewTrans ih1 ih2
  case appFunction q r a h ih => exact .some _ _ _ _ h (.refl _)
  case appArgument q a b h ih => exact .some _ _ _ _ (.refl _) h
  all_goals first | exact .none | trivial

theorem actualPrimaryApplicationComponents : NumberedPrimaryShapesTargets.ActualPrimaryApplicationComponents := by
  intro Symbol arity symbols S Gamma sigma tau f a q
  constructor
  · intro h
    have hv := primaryAppView h
    obtain ⟨rho,q⟩ := q
    cases q with
    | app g b =>
      cases hv with
      | some _ _ _ _ hf ha =>
        have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation Symbol arity Gamma _ _
          (NumberedWindowEquivalenceProof.actualPrimaryErasure Symbol arity symbols S Gamma _ _ hf)
        obtain ⟨rfl,rfl⟩ := Ty.arrow.inj ht
        exact ⟨g,b,rfl,hf,ha⟩
    | var => cases hv
    | lam => cases hv
    | bottom => cases hv
    | ordinary => cases hv
    | numbered => cases hv
  · rintro ⟨g,b,rfl,hf,ha⟩
    exact .trans (.appFunction f g a hf) (.appArgument g a b ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryShapesProof
