module
public import LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputs
open ArbitraryHeadSharedWire (Valuation originalGraph)
open ArbitraryHeadFreshWireAllocation (Wire OriginalConjunction)

theorem knownNotOutput (known : List Nat) (wires : List Wire) (ht : Topological known wires)
    (n : Nat) (hk : n ∈ known) : n ∉ outputs wires := by
  induction wires generalizing known with
  | nil => simp [outputs]
  | cons w ws ih =>
      intro h
      change n ∈ w.output :: outputs ws at h
      rcases List.mem_cons.mp h with eq | rest
      · exact ht.2.1 (eq ▸ hk)
      · exact ih (w.output :: known) ht.2.2 (List.mem_cons_of_mem _ hk) rest

private theorem graphsCons (f : Nat → Nat) (w : Wire) (ws : List Wire) (final : Valuation) :
    OriginalConjunction f final (w :: ws) ↔
      reader f w final = some (final w.output) ∧ OriginalConjunction f final ws := by
  constructor
  · intro h
    exact ⟨h w List.mem_cons_self,fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
  · rintro ⟨atHead,atTail⟩ q hq
    rcases List.mem_cons.mp hq with he | tail
    · subst q
      exact atHead
    · exact atTail q tail

private theorem tailToAll (w : Wire) (ws : List Wire) (base final : Valuation) (v : Nat)
    (h : LeavesExternal ws (Function.update base w.output v) final) :
    LeavesExternal (w :: ws) base final := by
  intro n absence
  have nOut : n ≠ w.output := by
    intro equal
    subst n
    exact absence List.mem_cons_self
  have nTail : n ∉ outputs ws := fun hn => absence (List.mem_cons_of_mem _ hn)
  exact (h n nTail).trans (Function.update_of_ne nOut v base)

private theorem allToTail (w : Wire) (ws : List Wire) (base final : Valuation)
    (h : LeavesExternal (w :: ws) base final) :
    LeavesExternal ws (Function.update base w.output (final w.output)) final := by
  intro n nTail
  by_cases same : n = w.output
  · subst n
    exact (Function.update_self w.output (final w.output) base).symm
  · rw [Function.update_of_ne same]
    apply h n
    intro mem
    change n ∈ w.output :: outputs ws at mem
    exact (List.mem_cons.mp mem).elim same nTail

theorem exactSequentialOutputs : ExactSequentialOutputs := by
  intro f known wires
  induction wires generalizing known with
  | nil =>
      intro _ base final
      constructor
      · intro h
        have same : base = final := Option.some.inj h
        subst final
        exact ⟨by simp [OriginalConjunction],fun _ _ => rfl⟩
      · rintro ⟨_,ext⟩
        change some base = some final
        apply congrArg some
        funext n
        exact (ext n (by simp [outputs])).symm
  | cons w ws ih =>
      intro top base final
      have sourceNe : w.source ≠ w.output := fun eq => top.2.1 (eq ▸ top.1)
      have sourceOutside := knownNotOutput (w.output :: known) ws top.2.2 w.source
        (List.mem_cons_of_mem _ top.1)
      have outputOutside := knownNotOutput (w.output :: known) ws top.2.2 w.output List.mem_cons_self
      constructor
      · intro succeeds
        cases h : reader f w base with
        | none => simp [run,h] at succeeds
        | some v =>
            let middle := Function.update base w.output v
            have step : run f middle ws = some final := by simpa only [run,h,middle] using succeeds
            obtain ⟨tailGraph,tailOutside⟩ := (ih _ top.2.2 middle final).mp step
            have hs : final w.source = base w.source :=
              (tailOutside _ sourceOutside).trans (Function.update_of_ne sourceNe v base)
            have ho : final w.output = v :=
              (tailOutside _ outputOutside).trans (Function.update_self w.output v base)
            have headGraph : reader f w final = some (final w.output) := by
              unfold reader at h ⊢
              rw [hs,ho]
              exact h
            exact ⟨(graphsCons f w ws final).mpr ⟨headGraph,tailGraph⟩,
              tailToAll w ws base final v tailOutside⟩
      · rintro ⟨original,external⟩
        obtain ⟨headGraph,tailGraph⟩ := (graphsCons f w ws final).mp original
        let v := final w.output
        let middle := Function.update base w.output v
        have tailOutside : LeavesExternal ws middle final := allToTail w ws base final external
        have hs : final w.source = base w.source :=
          (tailOutside _ sourceOutside).trans (Function.update_of_ne sourceNe v base)
        have head : reader f w base = some v := by
          unfold reader at headGraph ⊢
          rw [hs] at headGraph
          exact headGraph
        have tailRun := (ih _ top.2.2 middle final).mpr ⟨tailGraph,tailOutside⟩
        simpa only [run,head,middle] using tailRun

theorem exactFailureAndUniqueOutputs : ExactFailureAndUniqueOutputs := by
  intro f known wires top base
  have compare := exactSequentialOutputs f known wires top base
  refine ⟨?_,?_,?_⟩
  · constructor
    · rintro absent ⟨final,h⟩
      have success := (compare final).mpr h
      rw [absent] at success
      cases success
    · intro noActual
      cases hx : run f base wires with
      | none => rfl
      | some final => exact (noActual ⟨final,(compare final).mp hx⟩).elim
  · constructor
    · intro success
      cases hx : run f base wires with
      | none => exact (success hx).elim
      | some final =>
          refine ⟨final,(compare final).mp hx,?_⟩
          intro other h
          exact Option.some.inj (((compare other).mpr h).symm.trans hx)
    · rintro ⟨final,h,_⟩ absent
      have success := (compare final).mpr h
      rw [absent] at success
      cases success
  · intro final h n hn
    exact ((compare final).mp h).2 n (knownNotOutput known wires top n hn)

end LogicLineages.PermittedControl.ArbitraryHeadSequentialOutputs
