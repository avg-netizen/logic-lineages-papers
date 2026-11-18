module
public import LogicLineages.CartierObserverCurrent.FiniteProfileDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FiniteProfile.Targets

def ActualFiniteProfile : Prop := ∀ d : Nat, Finite (Profile d)

def ActualGeometricBijection : Prop := ∀ d : Nat,
  ∃ e : State d ≃ Profile d, ∀ g : State d,
    ProfileDescent.extend d g.val = RationalCoverage.reconstruct d (e g).val

def ActualFiniteState : Prop := ∀ d : Nat, Finite (State d)
end LogicLineages.CartierObserverCurrent.FiniteProfile.Targets
