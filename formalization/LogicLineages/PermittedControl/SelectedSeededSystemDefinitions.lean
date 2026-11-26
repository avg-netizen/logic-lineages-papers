module
public import LogicLineages.PermittedControl.SelectedSeededCompilerDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemDefinitions
@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSeededSystem
open OrdinalComparison Source SelectedSourceDomain SelectedFunctionalDetector Source.AdmissibleSum
open Source.FunctionalHardnessCompletion

def Solves {n : Nat} (ctrl : Nat → Nat) (s : System n)
    (ρ : AdmissibleSubstitution ctrl (SignedPair.Context n)) : Prop :=
  ∀ d ∈ s, SignedPair.meaning (SelectedSeededCompiler.seededInputs ctrl ρ)
    (SeededCompiler.subtractSeed d)=0

def universalStrict {n : Nat} (ctrl : Nat → Nat) (policy : Policy) (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution ctrl (SeededSystem.compile s).context,
    groundValue ctrl policy ρ (SeededSystem.strictPair s).2 <
      groundValue ctrl policy ρ (SeededSystem.strictPair s).1

def universalWeak {n : Nat} (ctrl : Nat → Nat) (policy : Policy) (s : System n) : Prop :=
  ∀ ρ : AdmissibleSubstitution ctrl (SeededSystem.compile s).context,
    groundValue ctrl policy ρ (SeededSystem.weakPair s).1 ≤
      groundValue ctrl policy ρ (SeededSystem.weakPair s).2

/-- Literal signed zero equation used to compare the source's empty-system augmentation. -/
def zeroEquation (n : Nat) : SignedPair.Expression n := .add .unit (.neg .unit)
def augmentEmpty {n : Nat} (s : System n) : System n :=
  if s.isEmpty then [zeroEquation n] else s
end LogicLineages.PermittedControl.SelectedSeededSystem
