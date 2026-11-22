module
public import LogicLineages.PermittedControl.OriginalMixedGateNormalizationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedGateNormalization
open ArbitraryHeadFreshWireAllocation (Wire attach install strip)
open ArbitraryHeadWireList (hiddenNames)
open OriginalMixedGateSequential (Gate)

theorem attachShape (wires : List Wire) (n : Nat) :
    (attach n wires).map strip = wires := by
  induction wires generalizing n with
  | nil => rfl
  | cons w ws ih =>
      change w :: (attach (n+1) ws).map strip = w :: ws
      rw [ih]

private theorem listMaxSeed (xs : List Nat) (m : Nat) : m ≤ xs.foldr max m := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact ih.trans (le_max_right _ _)

private theorem listMaxOfMem (xs : List Nat) (m n : Nat) (mem : n ∈ xs) :
    n ≤ xs.foldr max m := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
      rcases List.mem_cons.mp mem with eq | ht
      · subst n
        exact le_max_left _ _
      · exact (ih ht).trans (le_max_right _ _)

private theorem catches (ext : Nat) (gates : List Gate) (g : Gate) (hg : g ∈ gates) :
    g.output ≤ protectedCeiling ext gates ∧ ∀ n ∈ g.references, n ≤ protectedCeiling ext gates := by
  constructor
  · exact listMaxOfMem (listedNames gates) ext g.output
      (List.mem_append_left _ (List.mem_map.mpr ⟨g,hg,rfl⟩))
  · intro n hn
    exact listMaxOfMem (listedNames gates) ext n
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨g,hg,hn⟩))

private theorem attachHidden (wires : List Wire) (n : Nat) :
    (hiddenNames (attach n wires)).Nodup ∧ ∀ i ∈ hiddenNames (attach n wires), n ≤ i := by
  induction wires generalizing n with
  | nil => simp [attach,hiddenNames]
  | cons w ws ih =>
      obtain ⟨nodup,floor⟩ := ih (n+1)
      cases h : (install w n).finite with
      | true =>
          have names : hiddenNames (attach n (w :: ws)) = hiddenNames (attach (n+1) ws) := by
            simp only [attach,hiddenNames,List.filterMap_cons,ArbitraryHeadWireList.Gate.hiddenName,h]
          rw [names]
          exact ⟨nodup,fun i hi => (Nat.le_succ n).trans (floor i hi)⟩
      | false =>
          have names : hiddenNames (attach n (w :: ws)) = n :: hiddenNames (attach (n+1) ws) := by
            simp only [attach,hiddenNames,List.filterMap_cons,ArbitraryHeadWireList.Gate.hiddenName,h] <;> rfl
          rw [names]
          refine ⟨List.nodup_cons.mpr ⟨?_,nodup⟩,?_⟩
          · intro hn
            have impossible := floor n hn
            omega
          · intro i hi
            rcases List.mem_cons.mp hi with he | rest
            · subst i
              exact Nat.le_refl _
            · exact (Nat.le_succ n).trans (floor i rest)

private theorem collapseUsed (w : Wire) (gates : List Gate) (h : w ∈ collapseWires gates) :
    Gate.collapse w ∈ gates := by
  obtain ⟨g,hg,he⟩ := List.mem_filterMap.mp h
  cases g with
  | affine e n => simp [collapseWire] at he
  | collapse q =>
      have eq : q = w := Option.some.inj he
      subst q
      exact hg

theorem exactMixedFreshAliases : ExactMixedFreshAliases := by
  intro ext gates
  obtain ⟨nd,floor⟩ := attachHidden (collapseWires gates) (firstHidden ext gates)
  have beyond : ∀ n ∈ hiddenNames (collapseEntries ext gates),
      protectedCeiling ext gates < n := by
    intro n hn
    exact floor n hn
  refine ⟨listMaxSeed (listedNames gates) ext,fun g hg => catches ext gates g hg,
    ⟨nd,?_⟩,beyond⟩
  intro q hq
  have wIn : strip q ∈ collapseWires gates := by
    rw [← attachShape (collapseWires gates) (firstHidden ext gates)]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have outer := catches ext gates (Gate.collapse (strip q)) (collapseUsed (strip q) gates wIn)
  have a : q.source ≤ protectedCeiling ext gates := outer.2 q.source List.mem_cons_self
  have b : q.output ≤ protectedCeiling ext gates := outer.1
  exact ⟨fun hn => (Nat.not_lt_of_ge a) (beyond _ hn),fun hn => (Nat.not_lt_of_ge b) (beyond _ hn)⟩

end LogicLineages.PermittedControl.OriginalMixedGateNormalization
