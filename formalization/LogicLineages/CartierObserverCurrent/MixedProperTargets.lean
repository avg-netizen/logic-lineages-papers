module
public import LogicLineages.CartierObserverCurrent.MixedProperDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.MixedProper.Targets

def FractionProper : Prop :=
  ∀ (K : Type u) [Field K], ∀ P Q : Polynomial K,
    P.degree < Q.degree →
      proper (algebraMap (Polynomial K) (RatFunc K) P /
        algebraMap (Polynomial K) (RatFunc K) Q)

def DigitDegree : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ P Q : Polynomial K,
    P.degree < Q.degree → ∀ b : Bool,
      (Basic.actualPolynomialSquareRootDigit b (P * Q)).degree < Q.degree

def StepDigitIdentity : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ b : Bool, ∀ f : RatFunc K,
    step b f = Basic.actualRationalSquareRootDigit b f

def StepProper : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ b : Bool, ∀ f : RatFunc K,
    proper f → proper (step b f)

def StepDenominatorDivides : Prop :=
  ∀ (K : Type u) [Field K] [CharP K 2] [PerfectRing K 2], ∀ b : Bool, ∀ f : RatFunc K,
    (step b f).denom ∣ f.denom
end LogicLineages.CartierObserverCurrent.MixedProper.Targets
