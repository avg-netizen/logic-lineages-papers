module
public import LogicLineages.OrdinalComparison.ParametricOmegaFreeEvaluatorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Targets

def UniformComputable : Prop := ∀ H : Nat × Nat → Nat, Computable H →
  Computable (fun p : (Nat × List Nat) × Nat => evaluate H p.1.1 p.1.2 p.2)

def OmegaFreeCalibration : Prop := ∀ (ι : Type) (index : ι → Nat)
    (t : LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics.Term ι)
    (H : Nat × Nat → Nat) (i : Nat) (env : List Nat) (ρ : ι → Nat),
  SourceRestrictedAssignmentFinite.OmegaFree t → (∀ x, env.getD (index x) 0=ρ x) →
  (evaluate H i env (OrdinalSyntax.code index t) : Ordinal)=
    ParametricSourceSuccessor.denoteWith (fun n => H (i,n)) (fun x => (ρ x : Ordinal)) t

def TypedComponentCalibration : Prop := ∀ (Γ : List Ty) (t : OrdinalExpression Γ)
    (H : Nat × Nat → Nat) (i : Nat) (env : List Nat) (ρ : OrdinalComponent Γ → Nat),
  SourceRestrictedAssignmentFinite.OmegaFree t →
  (∀ c, env.getD (OrdinalSyntax.componentCode c) 0=ρ c) →
  (evaluate H i env (OrdinalSyntax.typedCode t) : Ordinal)=
    ParametricSourceSuccessor.denoteWith (fun n => H (i,n)) (fun c => (ρ c : Ordinal)) t
end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator.Targets
