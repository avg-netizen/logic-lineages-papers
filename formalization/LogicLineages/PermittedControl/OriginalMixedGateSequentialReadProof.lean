module
public import LogicLineages.PermittedControl.OriginalMixedGateSequentialTargets
import LogicLineages.PermittedControl.NaturalAffineGateGraphSemanticProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalMixedGateSequential
open ArbitraryHeadSharedWire (Valuation)
open NaturalAffineGateGraph (signedValue)

theorem exactMixedGateRead : ExactMixedGateRead := by
  constructor
  · intro f θ g
    cases g with
    | collapse w => rfl
    | affine e out =>
        have h := NaturalAffineGateGraph.signedGraph out e θ
        let s := signedValue e θ
        change (if 0 ≤ s then some s.toNat else none) = some (θ out) ↔
          (NaturalAffineGateGraph.graph out e).eval θ
        rw [h]
        by_cases good : 0 ≤ s
        · rw [if_pos good]
          have cast : (s.toNat : Int) = s := Int.toNat_of_nonneg good
          change some s.toNat = some (θ out) ↔ (θ out : Int) = s
          rw [Option.some.injEq]
          constructor
          · intro eq
            rw [← eq]
            exact cast
          · intro eq
            exact Int.ofNat_inj.mp (cast.trans eq.symm)
        · rw [if_neg good]
          change (none : Option Nat) = some (θ out) ↔ (θ out : Int) = s
          constructor
          · intro bad
            cases bad
          · intro eq
            exfalso
            exact good (by omega)
  · intro f θ e out
    let s := signedValue e θ
    change (if 0 ≤ s then some s.toNat else none) = none ↔ s < 0
    by_cases good : 0 ≤ s
    · rw [if_pos good]
      constructor
      · intro bad
        cases bad
      · intro bad
        exact (not_lt_of_ge good bad).elim
    · rw [if_neg good]
      exact ⟨fun _ => lt_of_not_ge good,fun _ => rfl⟩

theorem readCongruent (f : Nat → Nat) (g : Gate) (base final : Valuation)
    (agree : ∀ n ∈ g.references, final n = base n) :
    g.read f final = g.read f base := by
  cases g with
  | affine e n =>
      have inputs : e.2.map (fun t => t.1 * (final t.2 : Int)) =
          e.2.map (fun t => t.1 * (base t.2 : Int)) := by
        apply List.map_congr_left
        intro term hit
        have agreeAt := agree term.2 (List.mem_map.mpr ⟨term,hit,rfl⟩)
        rw [agreeAt]
      have summed : signedValue e final = signedValue e base := by
        simp only [signedValue,inputs]
      simp only [Gate.read,summed]
  | collapse w =>
      have atSource := agree w.source List.mem_cons_self
      change ArbitraryHeadSequentialOutputs.reader f w final =
        ArbitraryHeadSequentialOutputs.reader f w base
      unfold ArbitraryHeadSequentialOutputs.reader
      rw [atSource]

end LogicLineages.PermittedControl.OriginalMixedGateSequential
