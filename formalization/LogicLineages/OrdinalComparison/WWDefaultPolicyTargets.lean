module
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OrdinalSyntax

def DefaultPolicyPartialEquality : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ::Γ)),
    AdmissiblePartial.run defaultPolicy i t = AdmissiblePartial.run allLeftPolicy i t

def DefaultPolicyRepeatEquality : Prop :=
  ∀ (Γ : List Ty) (site : AdmissibleSum.MacroSite), site ≠ .optionalBoxTail →
    ∀ (count : Nat) (t : OrdinalExpression Γ),
      AdmissibleAssignment.repeated defaultPolicy site count t =
        AdmissibleAssignment.repeated allLeftPolicy site count t

def DefaultPolicyPositiveAggregation : Prop :=
  ∀ (n : Nat), defaultPolicy.shape .positiveAbstraction n = leftShape n

def DefaultPolicyBoxTail : Prop :=
  ∀ (Γ : List Ty) (n : Nat) (f g : OrdinalExpression Γ),
    AdmissibleAssignment.boxTail defaultPolicy n f g =
      if n=0 then .add f g else .add f (.add g (AdmissibleAssignment.numeral defaultPolicy n))
end LogicLineages.OrdinalComparison.Source.Targets
