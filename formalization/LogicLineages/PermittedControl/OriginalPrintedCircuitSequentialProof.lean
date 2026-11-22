module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialTargets
import LogicLineages.PermittedControl.OriginalPrintedCircuitSequentialReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitSequential
open ArbitraryHeadSharedWire (Valuation)

private theorem knownNotOutput (known : List Nat) (gates : List Gate)
    (ht : Topological known gates) (n : Nat) (hk : n ∈ known) : n ∉ outputs gates := by
  induction gates generalizing known with
  | nil => simp [outputs]
  | cons g gs ih =>
      intro h
      change n ∈ g.output :: outputs gs at h
      rcases List.mem_cons.mp h with eq | rest
      · exact ht.2.1 (eq ▸ hk)
      · exact ih (g.output :: known) ht.2.2 (List.mem_cons_of_mem _ hk) rest

private theorem graphsCons (f : Nat → Nat) (g : Gate) (gs : List Gate) (final : Valuation) :
    Graphs f final (g :: gs) ↔ g.read f final = Except.ok (final g.output) ∧ Graphs f final gs := by
  have hRead := exactCircuitGateReads.1 f g final
  constructor
  · intro h
    exact ⟨hRead.mpr (h g List.mem_cons_self),fun q hq => h q (List.mem_cons_of_mem _ hq)⟩
  · rintro ⟨atHead,atTail⟩ q hq
    rcases List.mem_cons.mp hq with he | tail
    · subst q
      exact hRead.mp atHead
    · exact atTail q tail

private theorem tailToAll (g : Gate) (gs : List Gate) (base final : Valuation) (v : Nat)
    (h : LeavesExternal gs (Function.update base g.output v) final) :
    LeavesExternal (g :: gs) base final := by
  intro n absence
  have nOut : n ≠ g.output := by
    intro equal
    subst n
    exact absence List.mem_cons_self
  have nTail : n ∉ outputs gs := fun hn => absence (List.mem_cons_of_mem _ hn)
  exact (h n nTail).trans (Function.update_of_ne nOut v base)

private theorem allToTail (g : Gate) (gs : List Gate) (base final : Valuation)
    (h : LeavesExternal (g :: gs) base final) :
    LeavesExternal gs (Function.update base g.output (final g.output)) final := by
  intro n nTail
  by_cases same : n = g.output
  · subst n
    exact (Function.update_self g.output (final g.output) base).symm
  · rw [Function.update_of_ne same]
    apply h n
    intro mem
    change n ∈ g.output :: outputs gs at mem
    exact (List.mem_cons.mp mem).elim same nTail

theorem exactPrintedCircuitRun : ExactPrintedCircuitRun := by
  intro f known gates
  induction gates generalizing known with
  | nil =>
      intro _ base final
      constructor
      · intro h
        have same : base = final := Except.ok.inj h
        subst final
        exact ⟨by simp [Graphs],fun _ _ => rfl⟩
      · rintro ⟨_,ext⟩
        change Except.ok base = Except.ok final
        apply congrArg Except.ok
        funext n
        exact (ext n (by simp [outputs])).symm
  | cons g gs ih =>
      intro top base final
      have oldReferences (v : Nat)
          (tailOutside : LeavesExternal gs (Function.update base g.output v) final) :
          ∀ n ∈ g.references, final n = base n := by
        intro n hit
        have inKnown := top.1 n hit
        have old := knownNotOutput (g.output :: known) gs top.2.2 n
          (List.mem_cons_of_mem _ inKnown)
        have diff : n ≠ g.output := fun h => top.2.1 (h ▸ inKnown)
        exact (tailOutside n old).trans (Function.update_of_ne diff v base)
      have outputOutside := knownNotOutput (g.output :: known) gs top.2.2 g.output List.mem_cons_self
      constructor
      · intro succeeds
        cases h : g.read f base with
        | error why => simp [run,h] at succeeds
        | ok v =>
            let middle := Function.update base g.output v
            have step : run f middle gs = Except.ok final := by simpa only [run,h,middle] using succeeds
            obtain ⟨tailGraph,tailOutside⟩ := (ih _ top.2.2 middle final).mp step
            have ho : final g.output = v :=
              (tailOutside _ outputOutside).trans (Function.update_self g.output v base)
            have head := exactCircuitGateReads.2.1 f g base final (oldReferences v tailOutside)
            have headGraph : g.read f final = Except.ok (final g.output) := by
              rw [head,ho]
              exact h
            exact ⟨(graphsCons f g gs final).mpr ⟨headGraph,tailGraph⟩,
              tailToAll g gs base final v tailOutside⟩
      · rintro ⟨original,external⟩
        obtain ⟨headGraph,tailGraph⟩ := (graphsCons f g gs final).mp original
        let v := final g.output
        let middle := Function.update base g.output v
        have tailOutside : LeavesExternal gs middle final := allToTail g gs base final external
        have head : g.read f base = Except.ok v :=
          (exactCircuitGateReads.2.1 f g base final (oldReferences v tailOutside)).symm.trans headGraph
        have tailRun := (ih _ top.2.2 middle final).mpr ⟨tailGraph,tailOutside⟩
        simpa only [run,head,middle] using tailRun

theorem exactPrintedCircuitFailureAndUniqueness : ExactPrintedCircuitFailureAndUniqueness := by
  intro f known gates top base
  have compare := exactPrintedCircuitRun f known gates top base
  refine ⟨?_,?_,?_⟩
  · constructor
    · rintro ⟨why,absent⟩ ⟨final,h⟩
      have success := (compare final).mpr h
      rw [absent] at success
      cases success
    · intro noActual
      cases hx : run f base gates with
      | error why => exact ⟨why,rfl⟩
      | ok final => exact (noActual ⟨final,(compare final).mp hx⟩).elim
  · constructor
    · rintro ⟨final,success⟩
      refine ⟨final,(compare final).mp success,?_⟩
      intro other h
      exact Except.ok.inj (((compare other).mpr h).symm.trans success)
    · rintro ⟨final,h,_⟩
      exact ⟨final,(compare final).mpr h⟩
  · intro final h n hn
    exact ((compare final).mp h).2 n (knownNotOutput known gates top n hn)

end LogicLineages.PermittedControl.OriginalPrintedCircuitSequential
