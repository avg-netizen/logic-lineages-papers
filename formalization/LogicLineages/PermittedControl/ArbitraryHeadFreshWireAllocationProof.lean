module
public import LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocationTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocation
open ArbitraryHeadWireList

private theorem attachShape (wires : List Wire) (n : Nat) :
    (attach n wires).map strip = wires := by
  induction wires generalizing n with
  | nil => rfl
  | cons w ws ih =>
      change w :: (attach (n+1) ws).map strip = w :: ws
      rw [ih]

private theorem wireLe (wires : List Wire) (w : Wire) (hw : w ∈ wires) :
    w.source ≤ maximum wires ∧ w.output ≤ maximum wires := by
  induction wires with
  | nil => simp at hw
  | cons head rest ih =>
      rcases List.mem_cons.mp hw with eq | tail
      · subst w
        exact ⟨(le_max_left _ _).trans (le_max_left _ _),
          (le_max_right _ _).trans (le_max_left _ _)⟩
      · obtain ⟨hs,ho⟩ := ih tail
        exact ⟨hs.trans (le_max_right _ _),ho.trans (le_max_right _ _)⟩

private theorem attachHidden (wires : List Wire) (n : Nat) :
    (hiddenNames (attach n wires)).Nodup ∧ ∀ i ∈ hiddenNames (attach n wires), n ≤ i := by
  induction wires generalizing n with
  | nil => simp [attach,hiddenNames]
  | cons w ws ih =>
      obtain ⟨nodup,floor⟩ := ih (n+1)
      cases h : (install w n).finite with
      | true =>
          have names : hiddenNames (attach n (w :: ws)) = hiddenNames (attach (n+1) ws) := by
            simp only [attach,hiddenNames,List.filterMap_cons,Gate.hiddenName,h] <;> rfl
          rw [names]
          exact ⟨nodup,fun i hi => (Nat.le_succ n).trans (floor i hi)⟩
      | false =>
          have names : hiddenNames (attach n (w :: ws)) = n :: hiddenNames (attach (n+1) ws) := by
            simp only [attach,hiddenNames,List.filterMap_cons,Gate.hiddenName,h] <;> rfl
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

theorem exactFreshAllocation : ExactFreshAllocation := by
  intro wires
  have shape : (allocate wires).map strip = wires := attachShape wires _
  obtain ⟨nd,floor⟩ := attachHidden wires (maximum wires+1)
  have beyond : ∀ i ∈ hiddenNames (allocate wires), maximum wires < i := by
    intro i hi
    exact floor i hi
  refine ⟨shape,⟨nd,?_⟩,beyond⟩
  intro g hg
  have hg' : strip g ∈ wires := by
    rw [← shape]
    exact List.mem_map.mpr ⟨g,hg,rfl⟩
  have both : g.source ≤ maximum wires ∧ g.output ≤ maximum wires :=
    wireLe wires (strip g) hg'
  exact ⟨fun mem => (Nat.not_lt_of_ge both.1) (beyond _ mem),
    fun mem => (Nat.not_lt_of_ge both.2) (beyond _ mem)⟩

end LogicLineages.PermittedControl.ArbitraryHeadFreshWireAllocation
