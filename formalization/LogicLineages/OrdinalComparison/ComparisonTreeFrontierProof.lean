module
public import LogicLineages.OrdinalComparison.ComparisonTreeTargets
public import LogicLineages.OrdinalComparison.ComparisonExpansionProgramProof
public import LogicLineages.OrdinalComparison.ComparisonTreeWellFoundedProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonTree

theorem frontier_program : Targets.ActualComparisonFrontierProgram := by
  have hs : Primrec encodedComparisonFrontierStep :=
    Primrec.list_flatMap Primrec.id
      (ComparisonExpansion.children_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have hi : Primrec₂ encodedComparisonFrontier :=
    Primrec.nat_iterate (α := (Nat × Nat) × Nat) (β := List (Nat × Nat)) Primrec.snd
      (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) (hs.comp Primrec.snd)
  exact ⟨hs,hi,fun root => ⟨rfl,fun k => Function.iterate_succ_apply' _ _ _⟩⟩

private theorem iterate_flatMap (n : Nat) (nodes : List (Nat × Nat)) :
    (encodedComparisonFrontierStep^[n]) nodes=
      nodes.flatMap (fun p => encodedComparisonFrontier p n) := by
  induction n with
  | zero => simp [encodedComparisonFrontier]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    change (nodes.flatMap (fun p => encodedComparisonFrontier p n)).flatMap
      (fun p => encodedComparisonChildren p.1 p.2)=_
    rw [List.flatMap_assoc]
    apply congrArg (fun f : (Nat × Nat) → List (Nat × Nat) => nodes.flatMap f)
    funext p
    exact (frontier_program.2.2 p).2 n |>.symm

private theorem frontier_children (root : Nat × Nat) (n : Nat) :
    encodedComparisonFrontier root (n+1)=
      (encodedComparisonChildren root.1 root.2).flatMap (fun p => encodedComparisonFrontier p n) := by
  unfold encodedComparisonFrontier
  rw [Function.iterate_succ_apply]
  have hs : encodedComparisonFrontierStep [root]=encodedComparisonChildren root.1 root.2 := by
    simp [encodedComparisonFrontierStep]
  rw [hs]
  exact iterate_flatMap n _

private theorem finite_uniform (nodes : List (Nat × Nat))
    (h : ∀ p∈nodes,∃ depth : Nat,∀ k≥depth,encodedComparisonFrontier p k=[]) :
    ∃ depth : Nat,∀ p∈nodes,∀ k≥depth,encodedComparisonFrontier p k=[] := by
  induction nodes with
  | nil => exact ⟨0,by simp⟩
  | cons p nodes ih =>
    obtain ⟨d,hd⟩ := h p (List.mem_cons_self)
    obtain ⟨e,he⟩ := ih (fun q hq => h q (List.mem_cons_of_mem p hq))
    refine ⟨max d e,?_⟩
    intro q hq k hk
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hd k ((Nat.le_max_left d e).trans hk)
    · exact he q hq k ((Nat.le_max_right d e).trans hk)

private theorem eventual_empty (root : Nat × Nat) :
    ∃ depth : Nat,∀ k≥depth,encodedComparisonFrontier root k=[] := by
  refine wellFounded.induction
    (C := fun root : Nat × Nat => ∃ depth : Nat,∀ k≥depth,encodedComparisonFrontier root k=[]) root ?_
  intro root ih
  obtain ⟨depth,hd⟩ := finite_uniform (encodedComparisonChildren root.1 root.2)
    (fun p hp => ih p hp)
  refine ⟨depth+1,?_⟩
  intro k hk
  have hk0 : 0<k := by omega
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk0)
  rw [frontier_children]
  apply List.flatMap_eq_nil_iff.mpr
  intro p hp
  exact hd p hp n (by omega)

theorem terminates : Targets.ActualComparisonFrontierTerminates := by
  intro root
  obtain ⟨depth,hd⟩ := eventual_empty root
  exact ⟨depth,hd depth le_rfl⟩

end LogicLineages.OrdinalComparison.ComparisonTree
