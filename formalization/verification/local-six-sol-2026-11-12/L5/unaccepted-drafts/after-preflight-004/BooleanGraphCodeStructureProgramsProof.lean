module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsDataProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeProof
open BooleanGraphCode NonlinearProjectionCompletion
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

/-- Literal radix arithmetic helpers; every argument is runtime data. -/
theorem quotient_primitive (b : Nat) : Primrec (fun code : Nat => code / b) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const b)
theorem tag_is (b n : Nat) : PrimrecPred (fun code : Nat => code % b = n) :=
  Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const b)) (Primrec.const n)
theorem left_primitive (b : Nat) : Primrec (fun code : Nat => (code / b).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp (quotient_primitive b))
theorem right_primitive (b : Nat) : Primrec (fun code : Nat => (code / b).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp (quotient_primitive b))
theorem binary_primitive (b tag : Nat) : Primrec₂ (fun a c : Nat => b * Nat.pair a c + tag) :=
  SourceBooleanProgramsProof.binary_primitive b tag
theorem unary_primitive (b tag : Nat) : Primrec (fun a : Nat => b * a + tag) :=
  SourceBooleanProgramsProof.unary_primitive b tag

def variablesAssemble (code : Nat) (values : List (List Nat)) : List Nat :=
  if code % 10 = 0 then [] else if code % 10 = 1 then [code / 10]
  else if code % 10 = 2 ∨ code % 10 = 3 then values.getD 0 [] ++ values.getD 1 []
  else values.getD 0 []

theorem variablesAssemble_primitive : Primrec₂ variablesAssemble := by
  let A := Nat × List (List Nat)
  have h0 : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite ((tag_is 10 0).comp Primrec.fst) (Primrec.const [])
    (Primrec.ite ((tag_is 10 1).comp Primrec.fst)
      (Primrec.list_cons.comp ((quotient_primitive 10).comp Primrec.fst) (Primrec.const []))
      (Primrec.ite (((tag_is 10 2).or (tag_is 10 3)).comp Primrec.fst)
        (Primrec.list_append.comp h0 h1) h0))

theorem variables_equation (code : Nat) : termVariables code = variablesAssemble code
    ((ExpandedGraphCodeProof.countChildren code).map termVariables) := by
  rw [termVariables]
  split_ifs <;> simp_all [ExpandedGraphCodeProof.countChildren, variablesAssemble]

theorem termVariables_computable : Computable termVariables := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat (List Nat)
    ExpandedGraphCodeProof.countChildren variablesAssemble id
    ExpandedGraphCodeProof.countChildren_primitive.to_comp variablesAssemble_primitive.to_comp
    Computable.id termVariables ExpandedGraphCodeProof.countChildren_decreasing variables_equation).2

/-- Every Boolean constructor contributes exactly its original recursive children. -/
def forestChildren (code : Nat) : List Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 ∨ code % 8 = 2 ∨ code % 8 = 3 ∨ code % 8 = 4 then []
  else if code % 8 = 5 then [code / 8]
  else [(code / 8).unpair.1, (code / 8).unpair.2]

def forestAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 then 0
  else if code % 8 = 2 ∨ code % 8 = 3 then WindowCode.add (code / 8).unpair.1 (code / 8).unpair.2
  else if code % 8 = 4 then (code / 8).unpair.2
  else if code % 8 = 5 then values.getD 0 0
  else WindowCode.add (values.getD 0 0) (values.getD 1 0)

theorem forestChildren_primitive : Primrec forestChildren :=
  Primrec.ite ((tag_is 8 0).or ((tag_is 8 1).or ((tag_is 8 2).or ((tag_is 8 3).or (tag_is 8 4)))))
    (Primrec.const [])
    (Primrec.ite (tag_is 8 5)
      (Primrec.list_cons.comp (quotient_primitive 8) (Primrec.const []))
      (Primrec.list_cons.comp (left_primitive 8)
        (Primrec.list_cons.comp (right_primitive 8) (Primrec.const []))))

theorem forestAssemble_primitive : Primrec₂ forestAssemble := by
  let A := Nat × List Nat
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (((tag_is 8 0).or (tag_is 8 1)).comp Primrec.fst) (Primrec.const 0)
    (Primrec.ite (((tag_is 8 2).or (tag_is 8 3)).comp Primrec.fst)
      ((binary_primitive 10 2).comp ((left_primitive 8).comp Primrec.fst) ((right_primitive 8).comp Primrec.fst))
      (Primrec.ite ((tag_is 8 4).comp Primrec.fst) ((right_primitive 8).comp Primrec.fst)
        (Primrec.ite ((tag_is 8 5).comp Primrec.fst) h0 ((binary_primitive 10 2).comp h0 h1))))

theorem forestChildren_decreasing : ∀ code child : Nat,
    child ∈ forestChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 8 = 0 ∨ code % 8 = 1 ∨ code % 8 = 2 ∨ code % 8 = 3 ∨ code % 8 = 4
  · simp [forestChildren, hleaf] at h
  have hp : 0 < code := by omega
  have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
  have hl := Nat.unpair_left_le (code / 8)
  have hr := Nat.unpair_right_le (code / 8)
  unfold forestChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

theorem forest_equation (code : Nat) : forest code =
    forestAssemble code ((forestChildren code).map forest) := by
  rw [forest]
  split_ifs <;> simp_all [forestChildren, forestAssemble]

theorem forest_computable : Computable forest := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph Nat Nat forestChildren forestAssemble id
    forestChildren_primitive.to_comp forestAssemble_primitive.to_comp Computable.id
    forest forestChildren_decreasing forest_equation).2

theorem foldMax_primitive : Primrec (fun xs : List Nat => xs.foldr max 0) := by
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem startFor_computable : Computable₂ startFor :=
  Primrec.succ.to_comp.comp
    (foldMax_primitive.to_comp.comp
      (Primrec.list_append.to_comp.comp Computable.fst
        (termVariables_computable.comp (forest_computable.comp Computable.snd))))

theorem allocated_computable : Computable₂ allocated :=
  ExpandedGraphCodeProof.allocated_computable.comp startFor_computable
    (forest_computable.comp Computable.snd)

#print axioms variablesAssemble_primitive
#print axioms variables_equation
#print axioms termVariables_computable
#print axioms forestChildren_primitive
#print axioms forestAssemble_primitive
#print axioms forestChildren_decreasing
#print axioms forest_equation
#print axioms forest_computable
#print axioms foldMax_primitive
#print axioms startFor_computable
#print axioms allocated_computable
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeProof
