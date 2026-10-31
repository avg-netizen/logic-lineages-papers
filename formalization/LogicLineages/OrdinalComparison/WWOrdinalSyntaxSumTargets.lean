module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def OrdinalSyntaxSumCorrect : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (f : Fin (n+1) → OrdinalExpression Γ),
    sumPrefix n (List.ofFn (fun j => typedCode (f j))) =
      typedCode (AdmissibleSum.expand (leftShape n) f)

def OrdinalSyntaxRepeatCorrect : Prop :=
  ∀ (Γ : List Ty) (site : AdmissibleSum.MacroSite) (count : Nat) (t : OrdinalExpression Γ),
    repeatCode count (typedCode t) = typedCode (AdmissibleAssignment.repeated allLeftPolicy site count t)

def OrdinalSyntaxSumOperationsPrimitiveRecursive : Prop :=
  Primrec₂ sumPrefix ∧ Primrec₂ repeatCode
end LogicLineages.OrdinalComparison.Source.Targets
