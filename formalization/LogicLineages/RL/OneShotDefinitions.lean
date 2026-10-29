module

public import LogicLineages.RL.InteractionDefinitions

/-! Paper 13, the three simple source environments following `lem:affine`,
and the two target nontriviality witnesses in `prop:positive`. Raw functions
are specified on all histories; admissibility and values are separate targets.
Source paper.tex SHA-256:
d3b396ff59814360751ad0b602c60a08d6602c7cce4a0459d3686e270ee660d8. -/
@[expose] public section

namespace LogicLineages.RL.Policy

/-- Initial z0; second percept z1 iff the recorded first action passes the
test; every other percept z0. The first percept recorded in an off-path
singleton history does not change the test. -/
def oneShot {S : Alphabet} (test : S.Action → Bool) : DEnvironment S
  | [(_, a)] => if test a then S.onePercept else S.zeroPercept
  | _ => S.zeroPercept

/-- Probability of passing the test after the actual initial zero percept. -/
def firstTestProbability {S : Alphabet} (p : SPolicy S)
    (test : S.Action → Bool) : ℚ :=
  ∑ a : S.Action, if test a then (p ([], S.zeroPercept)).mass a else 0

noncomputable def eqTest {S : Alphabet} (a₀ : S.Action) : S.Action → Bool := by
  classical
  exact fun a => decide (a = a₀)

noncomputable def neqTest {S : Alphabet} (a₀ : S.Action) : S.Action → Bool :=
  fun a => !(eqTest a₀ a)

def falseTest {S : Alphabet} : S.Action → Bool := fun _ => false
def trueTest {S : Alphabet} : S.Action → Bool := fun _ => true

end LogicLineages.RL.Policy
