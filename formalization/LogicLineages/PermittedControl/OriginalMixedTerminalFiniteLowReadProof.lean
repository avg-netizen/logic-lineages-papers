module
public import LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLowTargets
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationFreshProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLow
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees)
open OriginalMixedGateSequential (Gate run)
open OriginalMixedGateNormalization (collapseEntries exactMixedFreshAliases)
open OriginalMixedTerminalTest (Test testCeiling exactTerminalTestRead literalTestStable)

theorem exactFiniteTableLayout : ExactFiniteTableLayout := by
  intro f base rank bound gates p
  constructor
  · simp [table,List.map_map,Function.comp_def]
  · intro a hit
    rw [table,List.mem_map]
    constructor
    · rintro ⟨k,within,entry⟩
      have same : k = a := congrArg Prod.fst entry
      subst k
      exact ⟨List.mem_range.mp within,(congrArg Prod.snd entry).symm⟩
    · rintro ⟨within,rfl⟩
      exact ⟨a,List.mem_range.mpr within,rfl⟩

theorem actualResult (f : Nat → Nat) (base : Valuation) (rank a : Nat)
    (gates : List Gate) (p : Test) (admitted : p.Admitted)
    (final : Valuation) (positive : Bool) :
    result f base rank a gates p = some (final,positive) ↔
      run f (Function.update base rank a) gates = some final ∧ p.atPolarity positive final := by
  cases h : run f (Function.update base rank a) gates with
  | none =>
      constructor
      · intro impossible
        simp [result,h] at impossible
      · rintro ⟨impossible,_⟩
        cases impossible
  | some actual =>
      constructor
      · intro observed
        have equal : (actual,p.answer actual) = (final,positive) := by
          simpa only [result,h,Option.map_some,Option.some.injEq] using observed
        have state : actual = final := congrArg Prod.fst equal
        subst final
        exact ⟨rfl,(exactTerminalTestRead p admitted actual positive).mp (congrArg Prod.snd equal)⟩
      · rintro ⟨same,holds⟩
        have eq : actual = final := Option.some.inj same
        subst final
        have bool := (exactTerminalTestRead p admitted actual positive).mpr holds
        simp only [result,h,Option.map_some,bool]

private theorem maxSeed (xs : List Nat) (m : Nat) : m ≤ xs.foldr max m := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons _ _ ih => exact ih.trans (le_max_right _ _)

private theorem maxOfMem (xs : List Nat) (m n : Nat) (mem : n ∈ xs) : n ≤ xs.foldr max m := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
      rcases List.mem_cons.mp mem with eq | rest
      · subst n
        exact le_max_left _ _
      · exact (ih rest).trans (le_max_right _ _)

theorem lowLiftStability (known : List Nat) (rank : Nat) (p : Test) (gates : List Gate)
    (final lifted : Valuation)
    (same : Agrees (collapseEntries (lowCeiling known rank p) gates) final lifted) :
    (∀ name ∈ known, lifted name = final name) ∧ (∀ positive : Bool,
      p.atPolarity positive lifted ↔ p.atPolarity positive final) := by
  let ceiling := lowCeiling known rank p
  have fresh := exactMixedFreshAliases ceiling gates
  have sameWithin (n : Nat) (hb : n ≤ ceiling) : lifted n = final n :=
    same n (fun mem => (Nat.not_lt_of_ge (hb.trans fresh.1)) (fresh.2.2.2 n mem))
  refine ⟨fun name hn => sameWithin name (maxOfMem known _ name hn), ?_⟩
  have refs (n : Nat) (hn : n ∈ p.names) : n ≤ ceiling :=
    (maxOfMem p.names 0 n hn).trans ((le_max_right rank (testCeiling p)).trans (maxSeed known _))
  have stable := literalTestStable p final lifted (fun n hn => sameWithin n (refs n hn))
  intro positive
  cases positive
  · exact not_congr stable
  · exact stable

end LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLow
