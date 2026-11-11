module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepCasesProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction

def OrdinaryCases {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty}
    (q r : AuxTerm Symbol arity Gamma tau) : Prop :=
  match q, r with
  | .ordinary f base, r =>
      (∃ label : Nat, r = .numbered label f (headResult f) base [] .nil) ∨
      (∃ target : AuxArguments Symbol arity Gamma (headArguments arity f),
        WindowArgumentStep Symbol arity symbols S above Gamma (headArguments arity f) base target ∧
        r = .ordinary f target) ∨ r = .bottom (headResult f)
  | _, _ => True

theorem ordinaryCases {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {q r : AuxTerm Symbol arity Gamma tau} (h : WindowStep Symbol arity symbols S above Gamma tau q r) :
    OrdinaryCases symbols S above q r := by
  induction h using WindowStep.rec (motive_2 := fun _ _ _ _ _ => True)
  case put label f base => exact Or.inl ⟨label,rfl⟩
  case ordinaryArguments f base target h ih => exact Or.inr (Or.inl ⟨target,h,rfl⟩)
  case bottom q hn => cases q <;> first | exact Or.inr (Or.inr rfl) | trivial
  all_goals trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepCasesProof
