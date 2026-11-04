module
public import LogicLineages.OrdinalComparison.SourceGroundComponentEnvironmentDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment.Targets

def ExactLayout : Prop := ∀ xs : List Nat,
  (environment xs).length=bound xs.length ∧
  (∀ j : Nat, j<xs.length → (environment xs).getD (Nat.pair j 0) 0=xs.getD j 0) ∧
  (∀ k : Nat, k.unpair.2≠0 → (environment xs).getD k 0=0)

def TypedLookup : Prop := ∀ (Γ : List Ty) (xs : List Nat),
  SourceMachineRawValuations.AllGround Γ → xs.length=Γ.length →
  ∀ c : OrdinalComponent Γ,
    (environment xs).getD (OrdinalSyntax.componentCode c) 0=rawValuation xs c

def UniformPrimitiveRecursive : Prop :=
  Primrec bound ∧ Primrec (fun p : List Nat × Nat => slot p.1 p.2) ∧ Primrec environment
end LogicLineages.OrdinalComparison.Source.SourceGroundComponentEnvironment.Targets
