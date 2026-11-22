module
public import LogicLineages.PermittedControl.OriginalMixedTerminalTestTargets
import LogicLineages.PermittedControl.OriginalMixedTerminalTestReadProof
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationProof
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationFreshProof
import LogicLineages.PermittedControl.OriginalMixedGateSequentialProof
import LogicLineages.PermittedControl.ArbitraryHeadWireListAssignmentsProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedTerminalTest
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (extend extendAgrees)
open OriginalMixedGateNormalization
  (collapseEntries exactMixedNormalizedExtension exactMixedFreshAliases)
open OriginalMixedGateSequential (run exactMixedSequential)

private theorem leFoldMax (xs : List Nat) (name m : Nat) (mem : name ∈ xs) :
    name ≤ xs.foldr max m := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
      rcases List.mem_cons.mp mem with h | ht
      · subst name
        exact le_max_left _ _
      · exact (ih ht).trans (le_max_right _ _)

private theorem polarityStable (p : Test) (positive : Bool) (ν θ : Valuation)
    (h : p.eval θ ↔ p.eval ν) : p.atPolarity positive θ ↔ p.atPolarity positive ν := by
  cases positive
  · exact not_congr h
  · exact h

theorem exactProtectedTestLift : ExactProtectedTestLift := by
  intro gates p original
  let lifted := extend original (collapseEntries (testCeiling p) gates)
  have keeps (n : Nat) (mem : n ∈ p.names) : lifted n = original n := by
    have ceiling : n ≤ testCeiling p := leFoldMax p.names n 0 mem
    have fresh := exactMixedFreshAliases (testCeiling p) gates
    exact extendAgrees (collapseEntries (testCeiling p) gates) original n
      (fun mem => (Nat.not_lt_of_ge (ceiling.trans fresh.1)) (fresh.2.2.2 n mem))
  have stable := literalTestStable p original lifted keeps
  refine ⟨keeps,stable,?_⟩
  intro admitted
  have orig := (exactTerminalTestRead p admitted original (p.answer original)).mp rfl
  exact (exactTerminalTestRead p admitted lifted (p.answer original)).mpr
    ((polarityStable p (p.answer original) original lifted stable).mpr orig)

theorem exactObservedMixedTerminal : ExactObservedMixedTerminal := by
  intro f known gates top base p admitted
  let entries := collapseEntries (testCeiling p) gates
  have reading (θ : Valuation) (positive : Bool) := exactTerminalTestRead p admitted θ positive
  have lift (θ : Valuation) :=
    (exactMixedNormalizedExtension f (testCeiling p) gates θ).1
  have original (θ : Valuation) := exactMixedSequential f known gates top base θ
  have stable (θ : Valuation) (positive : Bool) :
      p.atPolarity positive (extend θ entries) ↔ p.atPolarity positive θ :=
    polarityStable p positive θ (extend θ entries) (exactProtectedTestLift gates p θ).2.1
  constructor
  · cases result : run f base gates <;> simp [observe,result]
  · intro positive
    constructor
    · intro observed
      cases result : run f base gates with
      | none => simp [observe,result] at observed
      | some final =>
          have answer : p.answer final = positive := by
            simpa only [observe,result,Option.map_some,Option.some.injEq] using observed
          obtain ⟨gatesHold,exterior⟩ := (original final).mp result
          have norm := (lift final (extend final entries)).mpr ⟨gatesHold,rfl⟩
          exact ⟨final,extend final entries,exterior,norm.1,norm.2,
            (stable final positive).mpr ((reading final positive).mp answer)⟩
    · rintro ⟨final,lifted,exterior,actual,agree,pass⟩
      obtain ⟨graphs,eq⟩ := (lift final lifted).mp ⟨actual,agree⟩
      subst lifted
      have success := (original final).mpr ⟨graphs,exterior⟩
      have answer := (reading final positive).mpr ((stable final positive).mp pass)
      simp only [observe,success,Option.map_some,answer]

end LogicLineages.PermittedControl.OriginalMixedTerminalTest
