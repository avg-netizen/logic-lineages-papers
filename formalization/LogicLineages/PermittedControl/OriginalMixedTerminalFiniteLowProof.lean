module
public import LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLowTargets
import LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLowReadProof
import LogicLineages.PermittedControl.OriginalMixedGateSequentialProof
import LogicLineages.PermittedControl.OriginalMixedGateNormalizationProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLow
open ArbitraryHeadSharedWire (Valuation)
open ArbitraryHeadWireList (Agrees extend)
open OriginalMixedGateSequential (Gate Topological run exactMixedSequential exactMixedFailureAndUniqueness)
open OriginalMixedGateNormalization (collapseEntries exactMixedNormalizedExtension)
open OriginalMixedTerminalTest (Test)

private theorem projectedResult (f : Nat → Nat) (known : List Nat) (gates : List Gate)
    (top : Topological known gates) (base : Valuation) (rank a : Nat) (external : rank ∈ known)
    (p : Test) (admitted : p.Admitted) (final : Valuation) (positive : Bool) :
    result f base rank a gates p = some (final,positive) ↔
      ProjectedAt f base known rank a gates p final positive := by
  let θ := Function.update base rank a
  let ceiling := lowCeiling known rank p
  let entries := collapseEntries ceiling gates
  have seq := exactMixedSequential f known gates top θ final
  have norm := (exactMixedNormalizedExtension f ceiling gates final).1
  have read := actualResult f base rank a gates p admitted final positive
  constructor
  · intro obs
    obtain ⟨runOK,testOK⟩ := read.mp obs
    obtain ⟨original,exterior⟩ := seq.mp runOK
    have externalEq (n : Nat) (hn : n ∈ known) : final n = θ n :=
      (exactMixedFailureAndUniqueness f known gates top θ).2.2 final runOK n hn
    have atRank : final rank = a :=
      (externalEq rank external).trans (Function.update_self _ _ _)
    let lifted := extend final entries
    have positiveGraph := (norm lifted).mpr ⟨original,rfl⟩
    have stable := lowLiftStability known rank p gates final lifted positiveGraph.2
    exact ⟨exterior,atRank,lifted,positiveGraph.1,positiveGraph.2,
      fun n hn => (stable.1 n hn).trans (externalEq n hn),(stable.2 positive).mpr testOK⟩
  · rintro ⟨exterior,_,lifted,graph,agree,_,testOK⟩
    have original := ((norm lifted).mp ⟨graph,agree⟩).1
    have same := lowLiftStability known rank p gates final lifted agree
    exact read.mpr ⟨seq.mpr ⟨original,exterior⟩,(same.2 positive).mp testOK⟩

theorem exactOriginalFiniteLowRows : ExactOriginalFiniteLowRows := by
  intro f known gates top base rank bound external p admitted
  have layout := (exactFiniteTableLayout f base rank bound gates p).2
  constructor
  · intro a
    rw [layout a none]
    have absent : none = result f base rank a gates p ↔
        run f (Function.update base rank a) gates = none := by
      cases h : run f (Function.update base rank a) gates <;> simp [result,h]
    exact and_congr Iff.rfl absent
  · intro a final positive
    rw [layout a (some (final,positive))]
    have compare := projectedResult f known gates top base rank a external p admitted final positive
    constructor
    · rintro ⟨within,h⟩
      exact ⟨within,compare.mp h.symm⟩
    · rintro ⟨within,h⟩
      exact ⟨within,(compare.mpr h).symm⟩

theorem exactOriginalFiniteLowPolarity : ExactOriginalFiniteLowPolarity := by
  intro f known gates top base rank bound external p admitted positive
  have rows := (exactOriginalFiniteLowRows f known gates top base rank bound external p admitted).2
  rw [anyPolarity,List.any_eq_true]
  constructor
  · rintro ⟨⟨a,out⟩,member,hit⟩
    cases out with
    | none => simp [Row.accepts] at hit
    | some state =>
        rcases state with ⟨final,b⟩
        have same : b = positive := by simpa [Row.accepts] using hit
        subst b
        obtain ⟨within,actual⟩ := (rows a final positive).mp member
        exact ⟨a,within,final,actual⟩
  · rintro ⟨a,within,final,actual⟩
    exact ⟨(a,some (final,positive)),(rows a final positive).mpr ⟨within,actual⟩,
      by simp [Row.accepts]⟩

end LogicLineages.PermittedControl.OriginalMixedTerminalFiniteLow
