module
public import LogicLineages.OrdinalComparison.CollectedPositiveDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def CollectedPositiveCodeInjective : Prop :=
  Function.Injective collectedPositiveEncode ∧ Function.Injective collectedTagsEncode

def CollectedPositiveTagIdentity : Prop :=
  ∀ (rho sigma : NONote) (A B : CollectedPositiveNF),
    collectedTagKey rho A=collectedTagKey sigma B ↔ rho=sigma ∧ A=B

def CollectedPositiveSupportExact : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags),
    CollectedPositiveValid (.mk c b tags) →
    (collectedPositiveSupport (.mk c b tags)=false ↔ b=0 ∧ tags=.nil)

def CollectedPositiveClosedValue : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags),
    CollectedPositiveValid (.mk c b tags) →
    collectedPositiveSupport (.mk c b tags)=false →
    ∀ x : Nat, actualCollectedPositiveEval (.mk c b tags) x=c

def CollectedPositiveHeightZero : Prop :=
  ∀ (c b : Nat) (tags : CollectedPositiveTags),
    collectedPositiveHeight (.mk c b tags)=0 ↔ tags=.nil

end LogicLineages.OrdinalComparison.Targets
