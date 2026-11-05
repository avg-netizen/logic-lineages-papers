module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationBaseProof
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesSupport
open CommonLayerSyntax CommonLayerComparison
abbrev Input := Nat × Nat

def children (p : Input) : List Input :=
  if p.1 = 0 then [] else (payload p.2).2.map (fun a => (p.1 - 1, a.2))
def assemble (p : Input) (xs : List (List Nat)) : List Nat :=
  if p.1 = 0 then BaseTermPrograms.variablesCode p.2 else xs.flatten

theorem decreasing (p : Input) (q : Input) (h : q ∈ children p) : q.1 < p.1 := by
  unfold children at h
  split_ifs at h with hz
  · simp at h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    omega

theorem equation (p : Input) : codedVariables p.1 p.2 =
    assemble p ((children p).map (fun q => codedVariables q.1 q.2)) := by
  rcases p with ⟨n, code⟩
  cases n with
  | zero => rfl
  | succ n =>
    simp [assemble, children, codedVariables, decodeCommon, commonVariables,
      List.flatMap_map, Function.comp_def, List.flatMap]

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem payload_primitive : Primrec payload :=
  Primrec.option_getD.comp (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Payload)))
    (Primrec.const (0, []))

theorem children_primitive : Primrec children := by
  have hs : Primrec (fun p : Input => (payload p.2).2) :=
    Primrec.snd.comp (payload_primitive.comp Primrec.snd)
  have hm : Primrec (fun p : Input => (payload p.2).2.map (fun a => (p.1 - 1, a.2))) :=
    Primrec.list_map hs ((Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 1)).pair
      (Primrec.snd.comp Primrec.snd)).to₂
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const []) hm

theorem assemble_computable : Computable₂ assemble := by
  have hb : Computable (fun p : Input × List (List Nat) => BaseTermPrograms.variablesCode p.1.2) :=
    BalancedBoxEvaluation.Base.actualComputation.2.comp (Computable.snd.comp Computable.fst)
  have hf : Computable (fun p : Input × List (List Nat) => p.2.flatten) :=
    Primrec.list_flatten.to_comp.comp Computable.snd
  apply (Computable.cond (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).decide.to_comp hb hf).of_eq
  intro p
  by_cases h : p.1.1 = 0 <;> simp [assemble, h]

theorem actualSupportProgram : CommonHeadExactVariablesTargets.ActualSupportProgram :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Input (List Nat) children assemble Prod.fst
    children_primitive.to_comp assemble_computable Computable.fst
    (fun p => codedVariables p.1 p.2) decreasing equation).2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesSupport
