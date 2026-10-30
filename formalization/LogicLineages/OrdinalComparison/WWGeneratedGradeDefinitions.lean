module
public import LogicLineages.OrdinalComparison.WWTypedPartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source

/-- Restricted grammar of generated assignment expressions, not the full
ambient C_i classes: no scalar promotion and no zero production. Membership
of actual canonical assignments must be proved separately. No norm condition
or original admissibility claim is encoded as an assumed field. -/
inductive GeneratedOrdinalGrade (Γ : List Ty) : Nat → OrdinalExpression Γ → Prop where
  | one (i : Nat) : GeneratedOrdinalGrade Γ i .one
  | omega (i : Nat) (hi : 0 < i) : GeneratedOrdinalGrade Γ i .omega
  | var {σ : Ty} (v : Variable Γ σ) (i : Fin (σ.level + 1)) :
      GeneratedOrdinalGrade Γ i.val (.var ⟨σ, v, i⟩)
  | add {i : Nat} {f g : OrdinalExpression Γ} :
      GeneratedOrdinalGrade Γ i f → GeneratedOrdinalGrade Γ i g →
        GeneratedOrdinalGrade Γ i (.add f g)
  | emul {i : Nat} {f g : OrdinalExpression Γ} :
      0 < i → GeneratedOrdinalGrade Γ (i + 1) f → GeneratedOrdinalGrade Γ i g →
        GeneratedOrdinalGrade Γ i (.emul f g)
  | collapse {f g : OrdinalExpression Γ} :
      GeneratedOrdinalGrade Γ 1 f → GeneratedOrdinalGrade Γ 0 g →
        GeneratedOrdinalGrade Γ 0 (.collapse f g)

end LogicLineages.OrdinalComparison.Source
