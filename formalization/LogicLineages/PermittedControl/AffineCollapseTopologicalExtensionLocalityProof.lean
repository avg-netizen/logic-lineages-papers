module
public import LogicLineages.PermittedControl.AffineCollapseTopologicalExtensionTargets
import LogicLineages.PermittedControl.AffineCollapseGraphCompositionPairProof
import LogicLineages.PermittedControl.NaturalAffineGateGraphSemanticProof

@[expose] public section
namespace LogicLineages.PermittedControl.AffineCollapseTopologicalExtension
open OrdinalComparison
open AffineCollapsePairListLow (Pair)

theorem knownNotBorn (known : List Nat) (pairs : List Pair) (top : Topological known pairs)
    (n : Nat) (belongs : n ∈ known) : n ∉ born pairs := by
  induction pairs generalizing known with
  | nil => simp [born]
  | cons p ps ih =>
      intro h
      rcases List.mem_cons.mp h with eq | rest
      · exact top.2.1 (eq ▸ belongs)
      · rcases List.mem_cons.mp rest with eq | later
        · exact top.2.2.1 (eq ▸ belongs)
        · exact ih (input p :: output p :: known) top.2.2.2.2
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ belongs)) later

theorem freshHead (known : List Nat) (p : Pair) (ps : List Pair)
    (top : Topological known (p :: ps)) :
    AffineCollapseGraphComposition.Fresh p.2.1 (input p) (output p) := by
  refine ⟨top.1,?_⟩
  intro t ht
  have seen := top.2.2.2.1 t ht
  exact ⟨fun h => top.2.1 (h ▸ seen),fun h => top.2.2.1 (h ▸ seen)⟩

theorem headExact (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
    (known : List Nat) (p : Pair) (ps : List Pair) (top : Topological known (p :: ps))
    (base : Valuation) (v : Nat × Nat) :
    graphAt f p (put p base v) ↔ domainAt p base ∧ v = valuesAt f p base :=
  (AffineCollapseGraphComposition.exactPairExtension f B selected (rawNoteEncode p.1.1)
    p.2.1 (input p) (output p) base (freshHead known p ps top)).1 v

private theorem putInput (p : Pair) (base : Valuation) (v : Nat × Nat)
    (diff : input p ≠ output p) : put p base v (input p) = v.1 := by
  rw [put,AffineCollapseGraphComposition.insertValues,Function.update_of_ne diff,Function.update_self]

private theorem putOutput (p : Pair) (base : Valuation) (v : Nat × Nat) :
    put p base v (output p) = v.2 :=
  Function.update_self _ _ _

theorem putOther (p : Pair) (base : Valuation) (v : Nat × Nat) (n : Nat)
    (nI : n ≠ input p) (nO : n ≠ output p) : put p base v n = base n := by
  rw [put,AffineCollapseGraphComposition.insertValues,Function.update_of_ne nO,Function.update_of_ne nI]

/-- Later writes leave the exact affine occurrences, the input, and the
output of this pair alone. No assumption forbids repeated dependencies. -/
theorem headGraphOfTailAgreement (f : Nat → Nat) (known : List Nat) (p : Pair) (ps : List Pair)
    (top : Topological known (p :: ps)) (middle final : Valuation)
    (agree : AgreesOutside ps middle final) :
    graphAt f p final ↔ graphAt f p middle := by
  have keep (n : Nat) (seen : n ∈ input p :: output p :: known) : final n = middle n :=
    agree n (knownNotBorn _ ps top.2.2.2.2 n seen)
  have hi : final (input p) = middle (input p) := keep _ List.mem_cons_self
  have ho : final (output p) = middle (output p) := keep _
    (List.mem_cons_of_mem _ List.mem_cons_self)
  have terms : p.2.1.2.map (fun t => t.1 * (final t.2 : Int)) =
      p.2.1.2.map (fun t => t.1 * (middle t.2 : Int)) := by
    apply List.map_congr_left
    intro t ht
    rw [keep _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (top.2.2.2.1 t ht)))]
  have sameAffine : NaturalAffineGateGraph.signedValue p.2.1 final =
      NaturalAffineGateGraph.signedValue p.2.1 middle := by
    simp only [NaturalAffineGateGraph.signedValue,terms]
  simp only [graphAt,AffineCollapseGraphComposition.graph,NaturalAffineGateGraph.signedGraph,
    hi,ho,sameAffine]

theorem extendTailAgreement (p : Pair) (ps : List Pair) (base final : Valuation)
    (diff : input p ≠ output p) (outside : AgreesOutside (p :: ps) base final) :
    AgreesOutside ps (put p base (final (input p),final (output p))) final := by
  intro n notLater
  by_cases nI : n = input p
  · subst n
    exact (putInput _ _ _ diff).symm
  by_cases nO : n = output p
  · subst n
    exact (putOutput _ _ _).symm
  have notAll : n ∉ born (p :: ps) := by
    intro h
    rcases List.mem_cons.mp h with h | h
    · exact nI h
    rcases List.mem_cons.mp h with h | h
    · exact nO h
    exact notLater h
  rw [putOther _ _ _ _ nI nO]
  exact outside n notAll

theorem restrictTailAgreement (p : Pair) (ps : List Pair) (base final : Valuation)
    (values : Nat × Nat) (outside : AgreesOutside ps (put p base values) final) :
    AgreesOutside (p :: ps) base final := by
  intro n absent
  have nI : n ≠ input p := by
    intro h
    subst n
    exact absent List.mem_cons_self
  have nO : n ≠ output p := by
    intro h
    subst n
    exact absent (List.mem_cons_of_mem _ List.mem_cons_self)
  have nTail : n ∉ born ps := fun h => absent (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h))
  exact (outside n nTail).trans (putOther _ _ _ _ nI nO)

end LogicLineages.PermittedControl.AffineCollapseTopologicalExtension
