module

public import LogicLineages.PersistentMarking.OrdinalArithmeticOrbitTargets

public section

namespace LogicLineages.PersistentMarking.OrdinalArithmeticOrbitProof
open OrdinalRealizationTargets OrdinalNativeIterationTargets OrdinalNativeOrbitProof
open OrdinalArithmeticOrbitTargets

def zeroValue : CountableOrdinal := ⟨0, by
  letI : IsEmpty {β : Ordinal.{0} // β < 0} :=
    ⟨fun β => not_lt_of_ge (show (0 : Ordinal.{0}) ≤ β.val from bot_le) β.property⟩
  infer_instance⟩

private theorem countableSuccessor (a : CountableOrdinal) :
    Countable {β : Ordinal.{0} // β < a.val + 1} := by
  have interval : Set.Iio (a.val + 1) = insert a.val (Set.Iio a.val) := by
    ext β
    simp only [Set.mem_Iio, Set.mem_insert_iff, Order.lt_add_one_iff]
    exact le_iff_eq_or_lt
  change (Set.Iio (a.val + 1)).Countable
  rw [interval]
  exact Set.Countable.insert a.val a.property

def successorValue (a : CountableOrdinal) : CountableOrdinal :=
  ⟨a.val + 1, countableSuccessor a⟩

noncomputable def additionValue (a b : CountableOrdinal) : CountableOrdinal :=
  orbit .base successorValue a b

noncomputable def multiplicationValue (a b : CountableOrdinal) : CountableOrdinal :=
  orbit .base (fun x => additionValue x a) zeroValue b

private theorem fullPrefixSup (lim : CountableOrdinal) (isLimit : Order.IsSuccLimit lim.val) :
    (⨆ β : EarlierStages lim, β.val) = lim.val := by
  letI : Countable (EarlierStages lim) := lim.property
  apply le_antisymm
  · exact Ordinal.iSup_le_iff.mpr fun β => β.property.le
  · apply le_of_not_gt
    intro below
    have smallSuccessor := isLimit.succ_lt below
    have successorLE := Ordinal.le_iSup (fun β : EarlierStages lim => β.val) ⟨_, smallSuccessor⟩
    exact (Order.lt_succ _).not_ge successorLE

theorem additionExact (a b : CountableOrdinal) : (additionValue a b).val = a.val + b.val := by
  have equations := orbitEquations .base successorValue a
  have allStages : ∀ (p : Ordinal.{0}) (count : Countable {β : Ordinal.{0} // β < p}),
      (additionValue a ⟨p, count⟩).val = a.val + p := by
    intro p
    induction p using Ordinal.limitRecOn with
    | zero =>
      intro count
      change (orbit .base successorValue a ⟨0, count⟩).val = a.val + 0
      rw [equations.1 ⟨0, count⟩ rfl, add_zero]
    | add_one p ih =>
      intro count
      let stage : CountableOrdinal := ⟨p + 1, count⟩
      let previous := earlierStage stage ⟨p, Order.lt_add_one_iff.mpr le_rfl⟩
      change (orbit .base successorValue a stage).val = a.val + (p + 1)
      rw [equations.2.1 previous stage rfl]
      change (additionValue a previous).val + 1 = a.val + (p + 1)
      have previousExact : (additionValue a previous).val = a.val + p := ih previous.property
      rw [previousExact, add_assoc]
    | limit p isLimit ih =>
      intro count
      let lim : CountableOrdinal := ⟨p, count⟩
      letI : Countable (EarlierStages lim) := count
      letI : Nonempty (EarlierStages lim) := ⟨⟨0, isLimit.pos⟩⟩
      have supEquation := equations.2.2 lim isLimit
      change (additionValue a lim).val =
        (⨆ β : EarlierStages lim, (additionValue a (earlierStage lim β)).val) at supEquation
      calc (additionValue a lim).val = (⨆ β : EarlierStages lim, (additionValue a (earlierStage lim β)).val) :=
            supEquation
        _ = (⨆ β : EarlierStages lim, a.val + β.val) := by
          exact congrArg (fun f : EarlierStages lim → Ordinal.{0} => ⨆ β, f β)
            (funext fun β => ih β.val β.property (earlierStage lim β).property)
        _ = a.val + p := by rw [← Ordinal.add_iSup, fullPrefixSup lim isLimit]
  exact allStages b.val b.property

theorem multiplicationExact (a b : CountableOrdinal) :
    (multiplicationValue a b).val = a.val * b.val := by
  let step := fun x => additionValue x a
  have equations := orbitEquations .base step zeroValue
  have allStages : ∀ (p : Ordinal.{0}) (count : Countable {β : Ordinal.{0} // β < p}),
      (multiplicationValue a ⟨p, count⟩).val = a.val * p := by
    intro p
    induction p using Ordinal.limitRecOn with
    | zero =>
      intro count
      change (orbit .base step zeroValue ⟨0, count⟩).val = a.val * 0
      rw [equations.1 ⟨0, count⟩ rfl, mul_zero] <;> rfl
    | add_one p ih =>
      intro count
      let stage : CountableOrdinal := ⟨p + 1, count⟩
      let previous := earlierStage stage ⟨p, Order.lt_add_one_iff.mpr le_rfl⟩
      change (orbit .base step zeroValue stage).val = a.val * (p + 1)
      rw [equations.2.1 previous stage rfl]
      change (additionValue (multiplicationValue a previous) a).val = a.val * (p + 1)
      have previousExact : (multiplicationValue a previous).val = a.val * p := ih previous.property
      rw [additionExact, previousExact, mul_add_one]
    | limit p isLimit ih =>
      intro count
      let lim : CountableOrdinal := ⟨p, count⟩
      letI : Countable (EarlierStages lim) := count
      have supEquation := equations.2.2 lim isLimit
      change (multiplicationValue a lim).val =
        (⨆ β : EarlierStages lim, (multiplicationValue a (earlierStage lim β)).val) at supEquation
      calc (multiplicationValue a lim).val =
            (⨆ β : EarlierStages lim, (multiplicationValue a (earlierStage lim β)).val) := supEquation
        _ = (⨆ β : EarlierStages lim, a.val * β.val) := by
          exact congrArg (fun f : EarlierStages lim → Ordinal.{0} => ⨆ β, f β)
            (funext fun β => ih β.val β.property (earlierStage lim β).property)
        _ = a.val * p := by rw [← Ordinal.mul_iSup, fullPrefixSup lim isLimit]
  exact allStages b.val b.property

theorem exact_OrdinalArithmeticOrbits : ExactOrdinalArithmeticOrbits :=
  ⟨zeroValue, successorValue, additionValue, multiplicationValue, rfl, fun _ => rfl,
    fun a b => ⟨rfl, additionExact a b⟩, fun a b => ⟨rfl, multiplicationExact a b⟩⟩

#print axioms exact_OrdinalArithmeticOrbits

end LogicLineages.PersistentMarking.OrdinalArithmeticOrbitProof
