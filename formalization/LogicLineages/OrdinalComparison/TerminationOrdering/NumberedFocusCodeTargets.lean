module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeTargets
open Source NumberedRewriteSyntax NumberedAuxiliaryCoding NumberedStepContexts
  NumberedTypedFocus NumberedFocusCode

/-- Exact focus metadata and value code, including every original failure. -/
def ActualFocusCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (path : List Position) (Gamma : List Ty)
    (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau),
    focusCode path Gamma tau (termCode q) =
      (focus path q).map (fun f => (f.holeGamma, f.holeType, termCode f.value))

/-- Replacing the discovered hole agrees with the original dependent context plug. -/
def ActualReplacementCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (path : List Position) (Gamma : List Ty)
    (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau) (f : TermFocus n arity Gamma tau)
    (replacement : AuxTerm (Fin n) arity f.holeGamma f.holeType),
    focus path q = some f →
      replaceCode path Gamma tau (termCode q) (termCode replacement) =
        some (termCode (plug f.context replacement))

/-- An invalid original path cannot produce a replacement, for any replacement code. -/
def ActualReplacementFailure : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (path : List Position) (Gamma : List Ty)
    (tau : Ty) (q : AuxTerm (Fin n) arity Gamma tau) (replacement : Code (Fin n)),
    focus path q = none → replaceCode path Gamma tau (termCode q) replacement = none

/-- Context, path, type and all raw syntax vary jointly. -/
def ActualFocusPrimitive : Prop :=
  ∀ n : Nat,
    Primrec (fun p : List Position × List Ty × Ty × Code (Fin n) =>
      focusCode p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Replacement is primitive recursive jointly with the full raw source input. -/
def ActualReplacementPrimitive : Prop :=
  ∀ n : Nat,
    Primrec (fun p : (List Position × List Ty × Ty × Code (Fin n)) × Code (Fin n) =>
      replaceCode p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFocusCodeTargets
