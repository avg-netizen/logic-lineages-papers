import LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentAddresses
import LogicLineages.PersistentMarking.NumberedWindowRules

namespace LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentComputabilityTargets
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowArithmeticLeastClass NumberedWindowConstructorArgumentAddresses

def PrimitiveReplacementComputableArguments : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) (source target : NArgs),
    (∀ q ∈ source.toList, ComputableArgument S K Γ hk q) → PrimitiveReplacement source target →
    ∀ q ∈ target.toList, ComputableArgument S K Γ hk q

def RawStepComputableArgument : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) (q r : NTerm),
    ComputableArgument S K Γ hk q → Typed (finiteC Γ) r r.type → RawStep S K q r →
    ComputableArgument S K Γ hk r

/-- A raw reduction in an actual base or extra argument preserves every
argument's computability. Lexical typing of the target is supplied by the
original typed constructor endpoint. Its window admission follows from the step. -/
def RawArgsStepComputableArguments : Prop :=
  ∀ S K Γ (hk : DecisionSourceUniverse.Closed K) (source target : NArgs),
    (∀ q ∈ source.toList, ComputableArgument S K Γ hk q) →
    (∀ r ∈ target.toList, Typed (finiteC Γ) r r.type) → RawArgsStep S K source target →
    ∀ r ∈ target.toList, ComputableArgument S K Γ hk r

end LogicLineages.PersistentMarking.NumberedWindowConstructorArgumentComputabilityTargets
