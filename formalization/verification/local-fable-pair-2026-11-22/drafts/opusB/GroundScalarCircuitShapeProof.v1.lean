module
public import LogicLineages.PermittedControl.GroundScalarCircuitTargets

public section
namespace LogicLineages.PermittedControl.GroundScalarCircuit
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.Source.ForwardTranslation (Scalar scalarHeadNote scalarCode)
open OriginalPrintedCircuitSequential (Gate Topological)
open PreparedProjection (PlainPreparedFormula)

theorem topoAppend : ∀ (known : List Nat) (gs gs' : List Gate),
    Topological known (gs ++ gs') ↔
      Topological known gs ∧ Topological ((gs.map Gate.output).reverse ++ known) gs'
  | known,[],gs' => by simp [Topological]
  | known,g :: gs,gs' => by
    simp only [List.cons_append,Topological,topoAppend (g.output :: known) gs gs',List.map_cons,
      List.reverse_cons,List.append_assoc,List.singleton_append,and_assoc]

theorem circuitOf_add {ι : Type} (index : ι → Nat) (a b : Scalar ι) (k : Nat) :
    circuitOf index (.add a b) k =
      ((circuitOf index a k).1 ++ (circuitOf index b (circuitOf index a k).2.2).1 ++
        [.base (.affine (0,[(1,(circuitOf index a k).2.1),
          (1,(circuitOf index b (circuitOf index a k).2.2).2.1)])
          (nodeName (circuitOf index b (circuitOf index a k).2.2).2.2))],
        nodeName (circuitOf index b (circuitOf index a k).2.2).2.2,
        (circuitOf index b (circuitOf index a k).2.2).2.2+1) := rfl

theorem circuitOf_shift {ι : Type} (index : ι → Nat) (c : OrdinalComparison.Source.ClosedPositive)
    (a : Scalar ι) (k : Nat) :
    circuitOf index (.shift c a) k =
      ((circuitOf index a k).1 ++
        [.base (.collapse ⟨scalarHeadNote c,(circuitOf index a k).2.1,nodeName (circuitOf index a k).2.2⟩)],
        nodeName (circuitOf index a k).2.2,(circuitOf index a k).2.2+1) := rfl

/-- Positions of the compiled circuit: counter grows, the output is one of
the gate outputs, every output is a fresh odd name in the counter range, and
the gate list is topological over any known list that contains the scalar's
input names and has no odd name at or above the start node. -/
theorem circuitFacts {ι : Type} (index : ι → Nat) : ∀ (s : Scalar ι) (k : Nat),
    k < (circuitOf index s k).2.2 ∧
    (circuitOf index s k).2.1 ∈ (circuitOf index s k).1.map Gate.output ∧
    (∀ m ∈ (circuitOf index s k).1.map Gate.output,
      m % 2 = 1 ∧ nodeName k ≤ m ∧ m < nodeName (circuitOf index s k).2.2) ∧
    ∀ L : List Nat, (∀ i ≤ scalarCode index s, inputName i ∈ L) →
      (∀ m ∈ L, m % 2 = 1 → m < nodeName k) → Topological L (circuitOf index s k).1
  | .one,k => by
    refine ⟨Nat.lt_succ_self k,List.mem_singleton.mpr rfl,?_,?_⟩
    · intro m hm
      have e : m = nodeName k := List.mem_singleton.mp hm
      subst e
      unfold nodeName
      omega
    · intro L _ hL
      refine ⟨fun n hn => ?_,fun h => ?_,trivial⟩
      · simp [Gate.references,OriginalMixedGateSequential.Gate.references] at hn
      · have := hL _ h (by unfold nodeName; omega)
        exact absurd this (Nat.lt_irrefl _)
  | .var x,k => by
    refine ⟨Nat.lt_succ_self k,List.mem_singleton.mpr rfl,?_,?_⟩
    · intro m hm
      have e : m = nodeName k := List.mem_singleton.mp hm
      subst e
      unfold nodeName
      omega
    · intro L hI hL
      refine ⟨fun n hn => ?_,fun h => ?_,trivial⟩
      · have e : n = inputName (index x) := by
          simpa [Gate.references,OriginalMixedGateSequential.Gate.references] using hn
        subst e
        exact hI (index x) (by show index x ≤ 4 * index x + 1; omega)
      · have := hL _ h (by unfold nodeName; omega)
        exact absurd this (Nat.lt_irrefl _)
  | .add a b,k => by
    have FA := circuitFacts index a k
    have FB := circuitFacts index b (circuitOf index a k).2.2
    have codeA : scalarCode index a ≤ scalarCode index (.add a b) := by
      show scalarCode index a ≤ 4 * Nat.pair (scalarCode index a) (scalarCode index b) + 2
      have := Nat.left_le_pair (scalarCode index a) (scalarCode index b)
      omega
    have codeB : scalarCode index b ≤ scalarCode index (.add a b) := by
      show scalarCode index b ≤ 4 * Nat.pair (scalarCode index a) (scalarCode index b) + 2
      have := Nat.right_le_pair (scalarCode index a) (scalarCode index b)
      omega
    rw [circuitOf_add]
    generalize circuitOf index a k = A at *
    generalize circuitOf index b A.2.2 = B at *
    obtain ⟨ka,oa,sa,ta⟩ := FA
    obtain ⟨kb,ob,sb,tb⟩ := FB
    have oaLt := (sa _ oa).2.2
    have obLt := (sb _ ob).2.2
    refine ⟨by omega,?_,?_,?_⟩
    · simp [List.map_append]
    · intro m hm
      simp only [List.map_append,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hm
      rcases hm with (h | h) | h
      · obtain ⟨h1,h2,h3⟩ := sa m h
        refine ⟨h1,h2,?_⟩
        unfold nodeName at *
        omega
      · obtain ⟨h1,h2,h3⟩ := sb m h
        refine ⟨h1,?_,?_⟩ <;> unfold nodeName at * <;> omega
      · subst h
        show (2 * B.2.2 + 1) % 2 = 1 ∧ nodeName k ≤ 2 * B.2.2 + 1 ∧ 2 * B.2.2 + 1 < nodeName (B.2.2 + 1)
        unfold nodeName
        omega
    · intro L hI hL
      rw [topoAppend,topoAppend]
      have hIa : ∀ i ≤ scalarCode index a, inputName i ∈ L := fun i hi => hI i (hi.trans codeA)
      have hIb : ∀ i ≤ scalarCode index b, inputName i ∈ L := fun i hi => hI i (hi.trans codeB)
      refine ⟨⟨ta L hIa hL,?_⟩,?_⟩
      · refine tb _ (fun i hi => List.mem_append_right _ (hIb i hi)) ?_
        intro m hm hodd
        rcases List.mem_append.mp hm with h | h
        · exact (sa m (List.mem_reverse.mp h)).2.2
        · have := hL m h hodd
          unfold nodeName at *
          omega
      · refine ⟨?_,?_,trivial⟩
        · intro n hn
          simp only [Gate.references,OriginalMixedGateSequential.Gate.references,List.map_cons,
            List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at hn
          rcases hn with h | h
          · subst h
            exact List.mem_append_left _ (List.mem_reverse.mpr
              (by rw [List.map_append]; exact List.mem_append_left _ oa))
          · subst h
            exact List.mem_append_left _ (List.mem_reverse.mpr
              (by rw [List.map_append]; exact List.mem_append_right _ ob))
        · intro hm
          change nodeName B.2.2 ∈ _ at hm
          rcases List.mem_append.mp hm with h | h
          · rw [List.mem_reverse,List.map_append,List.mem_append] at h
            rcases h with h | h
            · have := (sa _ h).2.2
              unfold nodeName at *
              omega
            · have := (sb _ h).2.2
              exact absurd this (Nat.lt_irrefl _)
          · have := hL _ h (by unfold nodeName; omega)
            unfold nodeName at *
            omega
  | .shift c a,k => by
    have FA := circuitFacts index a k
    have codeA : scalarCode index a ≤ scalarCode index (.shift c a) := by
      show scalarCode index a ≤
        4 * Nat.pair (OrdinalComparison.rawNoteEncode (scalarHeadNote c).1) (scalarCode index a) + 3
      have := Nat.right_le_pair (OrdinalComparison.rawNoteEncode (scalarHeadNote c).1) (scalarCode index a)
      omega
    rw [circuitOf_shift]
    generalize circuitOf index a k = A at *
    obtain ⟨ka,oa,sa,ta⟩ := FA
    refine ⟨by omega,?_,?_,?_⟩
    · simp [List.map_append]
    · intro m hm
      simp only [List.map_append,List.mem_append,List.map_cons,List.map_nil,List.mem_singleton] at hm
      rcases hm with h | h
      · obtain ⟨h1,h2,h3⟩ := sa m h
        refine ⟨h1,h2,?_⟩
        unfold nodeName at *
        omega
      · subst h
        show (2 * A.2.2 + 1) % 2 = 1 ∧ nodeName k ≤ 2 * A.2.2 + 1 ∧ 2 * A.2.2 + 1 < nodeName (A.2.2 + 1)
        unfold nodeName at *
        omega
    · intro L hI hL
      rw [topoAppend]
      refine ⟨ta L (fun i hi => hI i (hi.trans codeA)) hL,?_,?_,trivial⟩
      · intro n hn
        have e : n = A.2.1 := by
          simpa [Gate.references,OriginalMixedGateSequential.Gate.references] using hn
        subst e
        exact List.mem_append_left _ (List.mem_reverse.mpr oa)
      · intro hm
        change nodeName A.2.2 ∈ _ at hm
        rcases List.mem_append.mp hm with h | h
        · have := (sa _ (List.mem_reverse.mp h)).2.2
          exact absurd this (Nat.lt_irrefl _)
        · have := hL _ h (by unfold nodeName; omega)
          unfold nodeName at *
          omega

private theorem plainAtom (c : Int) (u v : Nat) (α β : Int) :
    PlainPreparedFormula (.atom (.nonnegative (c,[(α,.variable u),(β,.variable v)]))) := by
  intro a ha s hs
  have e : a = .nonnegative (c,[(α,.variable u),(β,.variable v)]) := List.mem_singleton.mp ha
  subst e
  rcases List.mem_cons.mp hs with h | h
  · subst h
    exact ⟨u,rfl⟩
  · have := List.mem_singleton.mp h
    subst this
    exact ⟨v,rfl⟩

theorem counterPlain (tag a b : Nat) : PlainPreparedFormula (counterFormula tag a b) := by
  unfold counterFormula
  split_ifs
  · exact plainAtom _ _ _ _ _
  · exact plainAtom _ _ _ _ _
  · intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact plainAtom _ _ _ _ _ x h
    · exact plainAtom _ _ _ _ _ x h

theorem blockShape : BlockShape := by
  intro ι index tag A B
  refine ⟨?_,counterPlain _ _ _⟩
  show Topological ((List.range (scalarCode index A + scalarCode index B + 1)).map inputName)
    ((circuitOf index A 0).1 ++ (circuitOf index B (circuitOf index A 0).2.2).1)
  have FA := circuitFacts index A 0
  have FB := circuitFacts index B (circuitOf index A 0).2.2
  generalize circuitOf index A 0 = CA at *
  obtain ⟨_,_,sa,ta⟩ := FA
  obtain ⟨_,_,_,tb⟩ := FB
  have inKnown : ∀ i ≤ scalarCode index A + scalarCode index B,
      inputName i ∈ (List.range (scalarCode index A + scalarCode index B + 1)).map inputName :=
    fun i hi => List.mem_map.mpr ⟨i,List.mem_range.mpr (by omega),rfl⟩
  have evenKnown : ∀ m ∈ (List.range (scalarCode index A + scalarCode index B + 1)).map inputName,
      m % 2 = 1 → False := by
    intro m hm hodd
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
    unfold inputName at hodd
    omega
  rw [topoAppend]
  refine ⟨ta _ (fun i hi => inKnown i (by omega)) (fun m hm hodd => (evenKnown m hm hodd).elim),?_⟩
  refine tb _ (fun i hi => List.mem_append_right _ (inKnown i (by omega))) ?_
  intro m hm hodd
  rcases List.mem_append.mp hm with h | h
  · exact (sa m (List.mem_reverse.mp h)).2.2
  · exact (evenKnown m h hodd).elim

#print axioms blockShape

end LogicLineages.PermittedControl.GroundScalarCircuit
