module
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.LiteralPartialDomain

/-- The literal partial recursion domain, not the smaller generated-source
syntax and not the original norm-admissible C_i predicate. Whole-free trees
are allowed at every grade, including the source's free scalar promotion.
The evaluator still tests whole-freeness before looking at constructors. -/
inductive Domain (Γ : List Ty) (σ : Ty) : Nat → OrdinalExpression (σ :: Γ) → Prop where
  | free (i : Nat) (t : OrdinalExpression (σ :: Γ)) :
      ordinalHeadFree t = true → Domain Γ σ i t
  | tracked (k : Fin (σ.level + 1)) : Domain Γ σ k.val (.var ⟨σ, .here, k⟩)
  | add {i : Nat} {f g : OrdinalExpression (σ :: Γ)} :
      Domain Γ σ i f → Domain Γ σ i g → Domain Γ σ i (.add f g)
  | emul {i : Nat} {f g : OrdinalExpression (σ :: Γ)} :
      0 < i → Domain Γ σ (i + 1) f → Domain Γ σ i g → Domain Γ σ i (.emul f g)
  | collapse {f g : OrdinalExpression (σ :: Γ)} :
      Domain Γ σ 1 f → Domain Γ σ 0 g → Domain Γ σ 0 (.collapse f g)

end LogicLineages.OrdinalComparison.Source.LiteralPartialDomain
