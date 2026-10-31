module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def OrdinalSyntaxHeadFreeCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ::Γ)),
    headFree (typedCode t) = ordinalHeadFree t

def OrdinalSyntaxHeadClosureCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ::Γ)),
    headClosure (typedCode t) = typedCode (ordinalHeadClosure t)

def OrdinalSyntaxPartialSizeCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ::Γ)),
    partialSize (typedCode t) = ordinalPartialSize t

def OrdinalSyntaxHeadOperationsPrimitiveRecursive : Prop :=
  Primrec headFree ∧ Primrec headClosure ∧ Primrec partialSize
end LogicLineages.OrdinalComparison.Source.Targets
