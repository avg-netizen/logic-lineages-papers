module
public import LogicLineages.CartierObserverCurrent.FullScalarProfileDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.FullScalarProfile.Targets
open SplittingRoots

/-- The selected coefficients are exactly the unique INITIAL genuine expansion. -/
def InitialMeaning : Prop := ∀ d : Nat, ∀ hd : 1 ≤ d, ∀ P : Polynomial (ZMod 2),
  ∀ hP : P.degree < (SourceBudget.denominator (ZMod 2) d).degree,
    InitialPrincipalParts.reconstruct d (SourceBudget.budget d) (initialCoefficients d hd P hP) =
      InitialPrincipalParts.source d P ∧
    ∀ b : InitialPrincipalParts.Coefficients d (SourceBudget.budget d),
      InitialPrincipalParts.reconstruct d (SourceBudget.budget d) b = InitialPrincipalParts.source d P →
      b = initialCoefficients d hd P hP

def ActualIterate : Prop := ∀ d : Nat, ∀ hd : 1 ≤ d, ∀ P : Polynomial (ZMod 2),
  ∀ hP : P.degree < (SourceBudget.denominator (ZMod 2) d).degree,
    ∀ ell : Nat, SourceBudget.transient d ≤ ell →
      ProfileDescent.extend d
        ((Basic.actualDifferentialCartier (K := ZMod 2))^[ell] (SourceObserver.initial d P)) =
      RationalCoverage.reconstruct d (evolvedBeta d hd P hP ell)

/-- Complete printed formula(O), with actual base canonical power-series coefficient. -/
def ScalarOutput : Prop := ∀ d : Nat, ∀ hd : 1 ≤ d, ∀ P : Polynomial (ZMod 2),
  ∀ hP : P.degree < (SourceBudget.denominator (ZMod 2) d).degree,
    ∀ ell : Nat, SourceBudget.transient d ≤ ell →
      RegularSelectors.regular
        ((Basic.actualDifferentialCartier (K := ZMod 2))^[ell] (SourceObserver.initial d P)) ∧
      algebraMap (ZMod 2) (FieldAt d)
        ((RegularSelectors.expansion
          ((Basic.actualDifferentialCartier (K := ZMod 2))^[ell] (SourceObserver.initial d P))).coeff 0) =
        ProfileOutput.value d (evolvedBeta d hd P hP ell)

def CompleteScalarProfile : Prop := InitialMeaning ∧ ActualIterate ∧ ScalarOutput
end LogicLineages.CartierObserverCurrent.FullScalarProfile.Targets
