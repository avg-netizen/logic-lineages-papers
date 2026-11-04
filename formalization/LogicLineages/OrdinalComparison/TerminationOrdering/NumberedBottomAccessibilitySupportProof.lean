module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilitySupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedQuotientPaths

def bottomView {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} (q : Packed Symbol arity Gamma) : Option Ty :=
  match q.2 with
  | .bottom tau => some tau
  | _ => none

theorem primaryBottomView {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S Gamma : List Ty}
    {q r : Packed Symbol arity Gamma} (h : WindowPrimary Symbol arity symbols S Gamma q r) : bottomView q = bottomView r := by
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => rfl
  case symm h ih => exact ih.symm
  case trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  all_goals first | rfl | trivial

theorem bottomViewRigid {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (q : Packed Symbol arity Gamma) (tau : Ty) (h : bottomView q = some tau) :
    q = ⟨tau,AuxTerm.bottom tau⟩ := by
  obtain ⟨rho,q⟩ := q
  cases q <;> simp_all [bottomView]
  cases h
  rfl

theorem noPositiveOfNoEdge {H : Nat → Nat → Prop} (x : Nat) (h : ∀ y, ¬ H x y) :
    ∀ y, ¬ PositivePath H x y := by
  have aux {a b : Nat} (hp : PositivePath H a b) : a ≠ x := by
    induction hp with
    | step he => intro hx; exact h _ (hx ▸ he)
    | trans h1 h2 ih1 ih2 => exact ih1
  intro y hp
  exact aux hp rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomAccessibilitySupportProof
