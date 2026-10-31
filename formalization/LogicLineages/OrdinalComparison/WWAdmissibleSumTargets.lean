module
public import LogicLineages.OrdinalComparison.WWAdmissibleSumDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

/-- Ordered unchanged leaf use, and exact binary-node count, for EVERY shape.
The +1 form avoids truncated subtraction: the inserted Add-node count is n−1. -/
def ActualAdmissibleSumSyntax : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (s : Shape n) (xs : Fin n → OrdinalExpression Γ),
    0 < n ∧ operands s xs = List.ofFn xs ∧
      ordinalLiteralNodes (expand s xs) + 1 =
        ((List.ofFn xs).map ordinalLiteralNodes).sum + n

/-- Arbitrary ordered associations preserve actual ordinal values of a fixed
operand list, including operands with collapse or variables. They do not
preserve the trees inspected by a later whole-free-first partial. -/
def ActualAdmissibleSumValue : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (s t : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (ρ : OrdinalComponent Γ → Ordinal),
    denote ρ (expand s xs) = denote ρ (expand t xs)

end LogicLineages.OrdinalComparison.Source.Targets
