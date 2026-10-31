module
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def DefaultPolicyAbstractionEquality : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ::Γ) m),
    AdmissibleAssignment.abstraction defaultPolicy h = AdmissibleAssignment.abstraction allLeftPolicy h

def DefaultSyntaxPartialCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ::Γ)),
    partialRun σ.level i (typedCode t) =
      (AdmissiblePartial.run defaultPolicy i t).map (fun v => List.ofFn (fun j => typedCode (v j)))

def DefaultSyntaxAbstractionCorrect : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (h : OrdinalVector (σ::Γ) m),
    abstractionCode σ.level m (vectorCode h) =
      (AdmissibleAssignment.abstraction defaultPolicy h).map vectorCode
end LogicLineages.OrdinalComparison.Source.Targets
