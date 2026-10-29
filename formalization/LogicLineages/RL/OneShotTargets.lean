module

public import LogicLineages.RL.OneShotDefinitions

/-! Independent one-shot semantic suppliers for source `prop:positive`.
No admissibility or value oracle is a premise of these complete targets. -/
@[expose] public section

namespace LogicLineages.RL.Policy.Targets

/-- Literal rules, including arbitrary off-path initial percepts and later
histories. No test can change the initial reward or rewards after the second. -/
def OneShotOffPathRule (S : Alphabet) : Prop :=
  ∀ test : S.Action → Bool,
    oneShot test [] = S.zeroPercept ∧
    (∀ z a, oneShot test [(z, a)] =
      if test a then S.onePercept else S.zeroPercept) ∧
    (∀ h : EnvHistory S, 2 ≤ h.length → oneShot test h = S.zeroPercept)

/-- The actual finite expectation has stabilized after the second percept,
for every stochastic policy, not just policies in a proposed image. -/
def OneShotFiniteValue (S : Alphabet) : Prop :=
  ∀ (test : S.Action → Bool) (p : SPolicy S) (n : ℕ), 2 ≤ n →
    finiteValue p (embedEnvironment (oneShot test)) n =
      (firstTestProbability p test : ℝ)

/-- Full all-policy (both kinds) admissibility of the literal raw map. -/
def OneShotAdmissible (S : Alphabet) : Prop :=
  ∀ test : S.Action → Bool, Admissible (embedEnvironment (oneShot test))

/-- Actual packaged environment and its exact values, with the same environment
working simultaneously for every stochastic and embedded deterministic policy. -/
def OneShotValue (S : Alphabet) : Prop :=
  ∀ test : S.Action → Bool,
    ∃ e : AdmissibleDEnvironment S, e.val = oneShot test ∧
      (∀ p : SPolicy S, value p (admissibleEmbedEnvironment e) =
        (firstTestProbability p test : ℝ)) ∧
      (∀ p : DPolicy S, value (embedPolicy p) (admissibleEmbedEnvironment e) =
        (firstTestProbability (embedPolicy p) test : ℝ))

/-- The source e+, e−, e0 and the policy-independent reward-one witness.
These are equal/not-equal/false/true action tests on genuine admissible maps.
No two-action assumption is needed for the environment-value calculations. -/
def OneShotSpecialValues (S : Alphabet) : Prop :=
  ∀ a₀ : S.Action,
    ∃ ePlus eMinus eZero eOne : AdmissibleDEnvironment S,
      ePlus.val = oneShot (eqTest a₀) ∧
      eMinus.val = oneShot (neqTest a₀) ∧
      eZero.val = oneShot (falseTest (S := S)) ∧
      eOne.val = oneShot (trueTest (S := S)) ∧
      ∀ p : SPolicy S,
        value p (admissibleEmbedEnvironment ePlus) =
          ((p ([], S.zeroPercept)).mass a₀ : ℝ) ∧
        value p (admissibleEmbedEnvironment eMinus) =
          1 - ((p ([], S.zeroPercept)).mass a₀ : ℝ) ∧
        value p (admissibleEmbedEnvironment eZero) = 0 ∧
        value p (admissibleEmbedEnvironment eOne) = 1

end LogicLineages.RL.Policy.Targets
