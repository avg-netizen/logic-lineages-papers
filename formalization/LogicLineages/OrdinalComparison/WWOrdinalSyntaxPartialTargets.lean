module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def OrdinalSyntaxPartialCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ::Γ)),
    partialRun σ.level i (typedCode t) =
      (AdmissiblePartial.run allLeftPolicy i t).map (fun v => List.ofFn (fun j => typedCode (v j)))

def OrdinalSyntaxPartialPrimitiveRecursive : Prop :=
  Primrec (fun p : Nat × Nat × Nat => partialRun p.1 p.2.1 p.2.2)
end LogicLineages.OrdinalComparison.Source.Targets
