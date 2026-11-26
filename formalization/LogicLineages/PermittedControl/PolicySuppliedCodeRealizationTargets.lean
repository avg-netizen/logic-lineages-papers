module
public import LogicLineages.PermittedControl.PolicySuppliedCodeMacroInterpreterTargets

@[expose] public section
namespace LogicLineages.PermittedControl.PolicySuppliedCodeRealization
open OrdinalComparison.Source.AdmissibleSum
open StandardControlCurrent
open PolicySuppliedCodeMacro (RealizesPolicy)

/-- Every policy admitted by the existing effectiveness predicate has an
ordinary program satisfying the literal selector realization relation. -/
def EffectiveHasCode : Prop :=
  ∀ p : Policy, PolicyShape.Effective p →
    ∃ e : Nat.Partrec.Code, RealizesPolicy e p

/-- A supplied code realizing the literal selector suffices for the
existing effectiveness predicate; no new policy class is introduced. -/
def RealizedIsEffective : Prop :=
  ∀ (e : Nat.Partrec.Code) (p : Policy), RealizesPolicy e p →
    PolicyShape.Effective p

/-- The supplied-code interface covers exactly the original effective
policies. It does not choose a code computably from a semantic policy or
assert a complete uniform source/compiler comparison theorem. -/
def ExactPolicyCodeRealization : Prop :=
  ∀ p : Policy, PolicyShape.Effective p ↔
    ∃ e : Nat.Partrec.Code, RealizesPolicy e p

end LogicLineages.PermittedControl.PolicySuppliedCodeRealization
