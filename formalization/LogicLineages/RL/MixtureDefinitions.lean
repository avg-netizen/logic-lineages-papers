module

public import LogicLineages.RL.InteractionDefinitions
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Paper 13 `eq:mixture` and `lem:mixture`, lines 275–312. Action-only
likelihood products are taken on the whole recorded history, not on one
interaction's support. The posterior distribution is implemented by a
normalized convex combination, with an explicit zero-denominator fallback.
Only constructor probability invariants are proved in this definitions file. -/
@[expose] public section

namespace LogicLineages.RL.Policy

abbrev RatOpenUnit := {w : ℚ // 0 < w ∧ w < 1}

/-- Product of probabilities of recorded actions at their recorded preceding
histories. There are no percept probabilities in this product. -/
def actionLikelihood {S : Alphabet} (p : SPolicy S) (h : EnvHistory S) : ℚ :=
  ∏ i : Fin h.length, (p (h.take i.val, (h.get i).1)).mass (h.get i).2

def mixtureDenominator {S : Alphabet} (w : RatOpenUnit)
    (p q : SPolicy S) (h : EnvHistory S) : ℚ :=
  w.val * actionLikelihood p h + (1 - w.val) * actionLikelihood q h

/-- Posterior weight of branch p. Its subtype proofs are solely constructor
invariants; the likelihood and interaction identities are independent targets. -/
def posteriorWeight {S : Alphabet} (w : RatOpenUnit) (p q : SPolicy S)
    (h : EnvHistory S) : RatUnit := by
  let d := mixtureDenominator w p q h
  have hp : 0 ≤ actionLikelihood p h :=
    Finset.prod_nonneg (fun i _ => (p (h.take i.val, (h.get i).1)).nonneg (h.get i).2)
  have hq : 0 ≤ actionLikelihood q h :=
    Finset.prod_nonneg (fun i _ => (q (h.take i.val, (h.get i).1)).nonneg (h.get i).2)
  have hwp : 0 ≤ w.val * actionLikelihood p h := mul_nonneg w.property.1.le hp
  have hwq : 0 ≤ (1 - w.val) * actionLikelihood q h :=
    mul_nonneg (sub_nonneg.mpr w.property.2.le) hq
  exact if hd : 0 < d then
    ⟨w.val * actionLikelihood p h / d, div_nonneg hwp hd.le,
      (div_le_one hd).mpr (le_add_of_nonneg_right hwq)⟩
    else zeroWeight

/-- Behavioral posterior mixture on all agent histories. The denominator
depends only on prior recorded actions; the current action kernels still see
the current percept. This is not pointwise averaging with constant weights. -/
noncomputable def behavioralMixture {S : Alphabet} (a₀ : S.Action)
    (w : RatOpenUnit) (p q : SPolicy S) : SPolicy S :=
  fun h => if 0 < mixtureDenominator w p q h.1 then
    kernelMix (posteriorWeight w p q h.1) (q h) (p h)
  else dirac a₀

def positiveCompletedHistory {S : Alphabet} :
    (n : ℕ) → PositiveTrace S n → EnvHistory S
  | 0, _ => []
  | n + 1, (z, a, rest) => (z, a) :: positiveCompletedHistory n rest

def traceCompletedHistory {S : Alphabet} : (n : ℕ) → Trace S n → EnvHistory S
  | 0, _ => []
  | n + 1, tr => positiveCompletedHistory n tr

/-- Environment likelihood factor on a fixed positive trace, allowing its
percept probabilities to depend on all previously recorded actions. -/
def positivePerceptLikelihood {S : Alphabet} (μ : SEnvironment S) :
    (n : ℕ) → EnvHistory S → PositiveTrace S n → ℚ
  | 0, h, z => (μ h).mass z
  | n + 1, h, (z, a, rest) =>
      (μ h).mass z * positivePerceptLikelihood μ n (h ++ [(z, a)]) rest

def tracePerceptLikelihood {S : Alphabet} (μ : SEnvironment S) :
    (n : ℕ) → Trace S n → ℚ
  | 0, _ => 1
  | n + 1, tr => positivePerceptLikelihood μ n [] tr

end LogicLineages.RL.Policy
