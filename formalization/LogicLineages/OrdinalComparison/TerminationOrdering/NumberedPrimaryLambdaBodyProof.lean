module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence

def lamView {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) : Option (Σ sigma : Ty, Packed Symbol arity (sigma :: Gamma)) :=
  match q with
  | ⟨_,.lam body⟩ => some ⟨_,⟨_,body⟩⟩
  | _ => none

inductive ViewRelated {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S Gamma : List Ty) :
    Option (Σ sigma : Ty, Packed Symbol arity (sigma :: Gamma)) →
    Option (Σ sigma : Ty, Packed Symbol arity (sigma :: Gamma)) → Prop where
  | none : ViewRelated symbols S Gamma none none
  | some (sigma : Ty) (q r : Packed Symbol arity (sigma :: Gamma)) :
      WindowPrimary Symbol arity symbols S (sigma :: Gamma) q r →
      ViewRelated symbols S Gamma (some ⟨sigma,q⟩) (some ⟨sigma,r⟩)

theorem viewRefl {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    (v : Option (Σ sigma : Ty, Packed Symbol arity (sigma :: Gamma))) : ViewRelated symbols S Gamma v v := by
  cases v with
  | none => exact .none
  | some p => exact .some p.1 p.2 p.2 (.refl _)

theorem viewSymm {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {x y : Option (Σ sigma : Ty, Packed Symbol arity (sigma :: Gamma))} (h : ViewRelated symbols S Gamma x y) :
    ViewRelated symbols S Gamma y x := by
  cases h with
  | none => exact .none
  | some sigma q r h => exact .some sigma r q (.symm h)

theorem viewTrans {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {x y z : Option (Σ sigma : Ty, Packed Symbol arity (sigma :: Gamma))}
    (h : ViewRelated symbols S Gamma x y) (k : ViewRelated symbols S Gamma y z) : ViewRelated symbols S Gamma x z := by
  cases h with
  | none => cases k; exact .none
  | some sigma q r h => cases k with
    | some _ _ s k => exact .some sigma q s (.trans h k)

theorem primaryLamView {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) :
    ViewRelated symbols S Gamma (lamView q) (lamView r) := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl q => exact viewRefl _
  case symm h ih => exact viewSymm ih
  case trans h1 h2 ih1 ih2 => exact viewTrans ih1 ih2
  case lam q r h ih => exact .some _ _ _ h
  all_goals first | exact .none | trivial

theorem actualPrimaryLambdaBody : NumberedPrimaryLambdaBodyTargets.ActualPrimaryLambdaBody := by
  intro Symbol arity symbols S Gamma sigma tau body q
  constructor
  · intro h
    have hv := primaryLamView h
    obtain ⟨rho,q⟩ := q
    cases q with
    | lam body' =>
      cases hv with
      | some _ _ _ hb =>
        have ht := NumberedPrimaryEquivalenceProof.primaryTypePreservation Symbol arity _ _ _
          (NumberedWindowEquivalenceProof.actualPrimaryErasure Symbol arity symbols S _ _ _ hb)
        cases ht
        exact ⟨body',rfl,hb⟩
    | var => cases hv
    | app => cases hv
    | bottom => cases hv
    | ordinary => cases hv
    | numbered => cases hv
  · rintro ⟨body',rfl,hb⟩
    exact .lam body body' hb

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyProof
