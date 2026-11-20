module

public import LogicLineages.PersistentMarking.OrdinalOmegaOrbitTargets
public import LogicLineages.PersistentMarking.OrdinalArithmeticOrbitProof

public section

namespace LogicLineages.PersistentMarking.OrdinalOmegaOrbitProof
open OrdinalRealizationTargets OrdinalNativeIterationTargets OrdinalNativeOrbitProof
open OrdinalArithmeticOrbitTargets OrdinalArithmeticOrbitProof OrdinalOmegaOrbitTargets
open scoped Ordinal

private theorem omegaCountable : Countable {β : Ordinal.{0} // β < ω} := by
  let ofNatural (n : Nat) : {β : Ordinal.{0} // β < ω} :=
    ⟨n, Ordinal.natCast_lt_omega0 n⟩
  apply Function.Surjective.countable (f := ofNatural)
  intro β
  obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp β.property
  exact ⟨n, Subtype.ext hn.symm⟩

def omegaValue : CountableOrdinal := ⟨ω, omegaCountable⟩

noncomputable def powerValue (mul : CountableOrdinal → CountableOrdinal → CountableOrdinal)
    (one a : CountableOrdinal) : CountableOrdinal :=
  orbit .base (fun x => mul x omegaValue) one a

noncomputable def fixValue (s f : CountableOrdinal → CountableOrdinal) (z : CountableOrdinal) :
    CountableOrdinal :=
  orbit .base f (s z) omegaValue

theorem powerExact {mul : CountableOrdinal → CountableOrdinal → CountableOrdinal}
    (hMul : ∀ a b, (mul a b).val = a.val * b.val)
    (one : CountableOrdinal) (oneVal : one.val = 1) (a : CountableOrdinal) :
    (powerValue mul one a).val = (ω : Ordinal.{0}) ^ a.val := by
  have equations := orbitEquations .base (fun x => mul x omegaValue) one
  have allStages : ∀ (p : Ordinal.{0}) (count : Countable {β : Ordinal.{0} // β < p}),
      (powerValue mul one ⟨p, count⟩).val = (ω : Ordinal.{0}) ^ p := by
    intro p
    induction p using Ordinal.limitRecOn with
    | zero =>
      intro count
      change (orbit .base (fun x => mul x omegaValue) one ⟨0, count⟩).val = (ω : Ordinal.{0}) ^ 0
      rw [equations.1 ⟨0, count⟩ rfl, Ordinal.opow_zero]
      exact oneVal
    | add_one p ih =>
      intro count
      let stage : CountableOrdinal := ⟨p + 1, count⟩
      let earlier := earlierStage stage ⟨p, Order.lt_add_one_iff.mpr le_rfl⟩
      change (orbit .base (fun x => mul x omegaValue) one stage).val = (ω : Ordinal.{0}) ^ (p + 1)
      rw [equations.2.1 earlier stage rfl]
      change (mul (powerValue mul one earlier) omegaValue).val = (ω : Ordinal.{0}) ^ (p + 1)
      have earlierExact : (powerValue mul one earlier).val = (ω : Ordinal.{0}) ^ p := ih earlier.property
      rw [hMul, earlierExact, Ordinal.opow_add_one] <;> rfl
    | limit p isLimit ih =>
      intro count
      let lim : CountableOrdinal := ⟨p, count⟩
      have supEquation := equations.2.2 lim isLimit
      change (powerValue mul one lim).val =
        (⨆ β : EarlierStages lim, (powerValue mul one (earlierStage lim β)).val) at supEquation
      calc (powerValue mul one lim).val =
            (⨆ β : EarlierStages lim, (powerValue mul one (earlierStage lim β)).val) := supEquation
        _ = (⨆ β : EarlierStages lim, (ω : Ordinal.{0}) ^ β.val) := by
          exact congrArg (fun f : EarlierStages lim → Ordinal.{0} => ⨆ β, f β)
            (funext fun β => ih β.val β.property (earlierStage lim β).property)
        _ = (ω : Ordinal.{0}) ^ p := (Ordinal.opow_limit Ordinal.omega0_ne_zero isLimit).symm
  exact allStages a.val a.property

private theorem orbitBoundedByEpsilon (pow : CountableOrdinal → CountableOrdinal)
    (hPow : ∀ a, (pow a).val = (ω : Ordinal.{0}) ^ a.val) (start : CountableOrdinal)
    {e : Ordinal.{0}} (initial : start.val ≤ e) (fixed : (ω : Ordinal.{0}) ^ e = e)
    (a : CountableOrdinal) :
    (orbit .base pow start a).val ≤ e := by
  have equations := orbitEquations .base pow start
  have allStages : ∀ (p : Ordinal.{0}) (count : Countable {β : Ordinal.{0} // β < p}),
      (orbit .base pow start ⟨p, count⟩).val ≤ e := by
    intro p
    induction p using Ordinal.limitRecOn with
    | zero =>
      intro count
      rw [equations.1 ⟨0, count⟩ rfl]
      exact initial
    | add_one p ih =>
      intro count
      let stage : CountableOrdinal := ⟨p + 1, count⟩
      let earlier := earlierStage stage ⟨p, Order.lt_add_one_iff.mpr le_rfl⟩
      change (orbit .base pow start stage).val ≤ e
      rw [equations.2.1 earlier stage rfl]
      change (pow (orbit .base pow start earlier)).val ≤ e
      rw [hPow, ← fixed]
      exact (Ordinal.isNormal_opow Ordinal.one_lt_omega0).monotone (ih earlier.property)
    | limit p isLimit ih =>
      intro count
      let lim : CountableOrdinal := ⟨p, count⟩
      letI : Countable (EarlierStages lim) := count
      have supEquation := equations.2.2 lim isLimit
      change (orbit .base pow start lim).val =
        (⨆ β : EarlierStages lim, (orbit .base pow start (earlierStage lim β)).val) at supEquation
      change (orbit .base pow start lim).val ≤ e
      rw [supEquation]
      exact Ordinal.iSup_le_iff.mpr (fun β => ih β.val β.property (earlierStage lim β).property)
  exact allStages a.val a.property

theorem nextLeast (s pow : CountableOrdinal → CountableOrdinal)
    (hSucc : ∀ a, (s a).val = a.val + 1) (hPow : ∀ a, (pow a).val = (ω : Ordinal.{0}) ^ a.val) :
    NextIsLeastEpsilon pow (fixValue s) := by
  intro z
  let step := orbit .base pow (s z)
  let value (β : EarlierStages omegaValue) := (step (earlierStage omegaValue β)).val
  letI : Countable (EarlierStages omegaValue) := omegaCountable
  letI : Nonempty (EarlierStages omegaValue) := ⟨⟨0, Ordinal.omega0_pos⟩⟩
  have equations := orbitEquations .base pow (s z)
  have entirePrefix : (step omegaValue).val = ⨆ β : EarlierStages omegaValue, value β :=
    equations.2.2 omegaValue Ordinal.isSuccLimit_omega0
  have above : z.val < (step omegaValue).val := by
    let first : EarlierStages omegaValue := ⟨0, Ordinal.omega0_pos⟩
    have initial : value first = z.val + 1 := by
      change (orbit .base pow (s z) (earlierStage omegaValue first)).val = z.val + 1
      rw [equations.1 (earlierStage omegaValue first) rfl, hSucc]
    calc z.val < z.val + 1 := Order.lt_add_one_iff.mpr le_rfl
      _ = value first := initial.symm
      _ ≤ (step omegaValue).val := by rw [entirePrefix]; exact Ordinal.le_iSup value first
  have closure : (ω : Ordinal.{0}) ^ (step omegaValue).val ≤ (step omegaValue).val := by
    have normal := Ordinal.isNormal_opow Ordinal.one_lt_omega0
    calc (ω : Ordinal.{0}) ^ (step omegaValue).val = (ω : Ordinal.{0}) ^ (⨆ β, value β) := by
          rw [entirePrefix]
      _ = (⨆ β, (ω : Ordinal.{0}) ^ value β) :=
          Order.IsNormal.map_iSup normal Ordinal.bddAbove_of_small
      _ ≤ (step omegaValue).val := by
        rw [entirePrefix]
        apply Ordinal.iSup_le_iff.mpr
        intro β
        have nextBelow : β.val + 1 < omegaValue.val := by
          rw [← Order.succ_eq_add_one]
          exact Ordinal.isSuccLimit_omega0.succ_lt β.property
        let later : EarlierStages omegaValue := ⟨β.val + 1, nextBelow⟩
        have nextValue : value later = (ω : Ordinal.{0}) ^ value β := by
          change (orbit .base pow (s z) (earlierStage omegaValue later)).val =
            (ω : Ordinal.{0}) ^ (orbit .base pow (s z) (earlierStage omegaValue β)).val
          rw [equations.2.1 (earlierStage omegaValue β) (earlierStage omegaValue later) rfl, hPow]
        rw [← nextValue]
        exact Ordinal.le_iSup value later
  refine ⟨⟨above, closure.antisymm (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)⟩, ?_⟩
  intro e he
  change z.val < e ∧ (ω : Ordinal.{0}) ^ e = e at he
  have startBound : (s z).val ≤ e := by
    rw [hSucc]
    exact Order.add_one_le_iff.mpr he.1
  exact orbitBoundedByEpsilon pow hPow (s z) startBound he.2 omegaValue

theorem exact_OrdinalOmegaOrbits : ExactOrdinalOmegaOrbits := by
  intro Z s add mul h
  let one := s Z
  have oneExact : one.val = 1 := by
    change (s Z).val = 1
    rw [h.2.1, h.1, zero_add]
  have powExact := powerExact (fun a b => (h.2.2.2 a b).2) one oneExact
  exact ⟨omegaValue, one, powerValue mul one, fixValue s,
    ⟨rfl, rfl, oneExact, fun a => ⟨rfl, powExact a⟩, fun _ _ => rfl⟩,
    nextLeast s (powerValue mul one) h.2.1 powExact⟩

theorem exact_OrdinalArithmeticThroughNext : ExactOrdinalArithmeticThroughNext := by
  obtain ⟨Z, s, add, mul, equ⟩ := exact_OrdinalArithmeticOrbits
  obtain ⟨w, one, pow, fix, omega, next⟩ := exact_OrdinalOmegaOrbits Z s add mul equ
  exact ⟨Z, s, add, mul, w, one, pow, fix, equ, omega, next⟩

#print axioms exact_OrdinalOmegaOrbits
#print axioms exact_OrdinalArithmeticThroughNext

end LogicLineages.PersistentMarking.OrdinalOmegaOrbitProof
