module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProof
public import Mathlib.Computability.Primrec.List
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem tag_primitive : Primrec (fun code : Nat => code % 10) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 10)
#print axioms tag_primitive

theorem quotient_primitive : Primrec (fun code : Nat => code / 10) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 10)
#print axioms quotient_primitive

theorem left_primitive : Primrec (fun code : Nat => (code / 10).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
#print axioms left_primitive

theorem right_primitive : Primrec (fun code : Nat => (code / 10).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
#print axioms right_primitive

theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 10 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
#print axioms tag_is

def countChildren (code : Nat) : List Nat :=
  if code % 10 = 0 ∨ code % 10 = 1 then []
  else if code % 10 = 2 ∨ code % 10 = 3 then [(code / 10).unpair.1, (code / 10).unpair.2]
  else if code % 10 = 4 ∨ code % 10 = 5 then [(code / 10).unpair.2]
  else [code / 10]

def countAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 10 = 0 ∨ code % 10 = 1 then 1
  else if code % 10 = 2 ∨ code % 10 = 3 then values.getD 0 0 + values.getD 1 0 + 1
  else if code % 10 = 8 then values.getD 0 0 + 2
  else values.getD 0 0 + 1

theorem countChildren_primitive : Primrec countChildren :=
  Primrec.ite ((tag_is 0).or (tag_is 1)) (Primrec.const [])
    (Primrec.ite ((tag_is 2).or (tag_is 3))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const [])))
      (Primrec.ite ((tag_is 4).or (tag_is 5))
        (Primrec.list_cons.comp right_primitive (Primrec.const []))
        (Primrec.list_cons.comp quotient_primitive (Primrec.const []))))
#print axioms countChildren_primitive

theorem countAssemble_primitive : Primrec₂ countAssemble := by
  let A := Nat × List Nat
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (((tag_is 0).or (tag_is 1)).comp Primrec.fst) (Primrec.const 1)
    (Primrec.ite (((tag_is 2).or (tag_is 3)).comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_add.comp h0 h1) (Primrec.const 1))
      (Primrec.ite ((tag_is 8).comp Primrec.fst)
        (Primrec.nat_add.comp h0 (Primrec.const 2))
        (Primrec.nat_add.comp h0 (Primrec.const 1))))
#print axioms countAssemble_primitive

theorem countChildren_decreasing : ∀ code child : Nat,
    child ∈ countChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 10 = 0 ∨ code % 10 = 1
  · simp [countChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 10 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 10)
  have hr := Nat.unpair_right_le (code / 10)
  unfold countChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega
#print axioms countChildren_decreasing

theorem count_equation (code : Nat) :
    nodeCount code = countAssemble code ((countChildren code).map nodeCount) := by
  rw [nodeCount]
  split_ifs <;> simp_all [countChildren, countAssemble]
#print axioms count_equation

theorem nodeCount_computable : Computable nodeCount := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat Nat countChildren countAssemble id
    countChildren_primitive.to_comp countAssemble_primitive.to_comp Computable.id
    nodeCount countChildren_decreasing count_equation).2
#print axioms nodeCount_computable

theorem allocated_computable : Computable₂ allocated := by
  have hn : Primrec₂ SourceTermGraph.names :=
    Primrec.list_map (Primrec.list_range.comp Primrec.snd)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  exact hn.to_comp.comp Computable.fst (nodeCount_computable.comp Computable.snd)
#print axioms allocated_computable

theorem output_computable : Computable₂ output :=
  Primrec.nat_sub.to_comp.comp
    (Primrec.nat_add.to_comp.comp Computable.fst (nodeCount_computable.comp Computable.snd))
    (Computable.const 1)
#print axioms output_computable

theorem actualAllocationPrograms : ExpandedGraphCodeTargets.ActualAllocationPrograms :=
  ⟨nodeCount_computable, allocated_computable, output_computable⟩
#print axioms actualAllocationPrograms


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
