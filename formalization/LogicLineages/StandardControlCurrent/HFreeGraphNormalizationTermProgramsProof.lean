module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeAllocationProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

/-- Child ordering is exactly the literal ordinal-term traversal, not a set. -/
def variablesAssemble (code : Nat) (values : List (List Nat)) : List Nat :=
  if code % 10 = 0 then []
  else if code % 10 = 1 then [code / 10]
  else if code % 10 = 2 ∨ code % 10 = 3 then values.getD 0 [] ++ values.getD 1 []
  else values.getD 0 []

theorem variablesAssemble_primitive : Primrec₂ variablesAssemble := by
  let A := Nat × List (List Nat)
  have h0 : Primrec (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite ((ExpandedGraphCodeProof.tag_is 0).comp Primrec.fst) (Primrec.const [])
    (Primrec.ite ((ExpandedGraphCodeProof.tag_is 1).comp Primrec.fst)
      (Primrec.list_cons.comp (ExpandedGraphCodeProof.quotient_primitive.comp Primrec.fst) (Primrec.const []))
      (Primrec.ite (((ExpandedGraphCodeProof.tag_is 2).or (ExpandedGraphCodeProof.tag_is 3)).comp Primrec.fst)
        (Primrec.list_append.comp h0 h1) h0))

theorem termVariables_equation (code : Nat) :
    Code.termVariables code = variablesAssemble code
      ((ExpandedGraphCodeProof.countChildren code).map Code.termVariables) := by
  rw [Code.termVariables]
  split_ifs <;> simp_all [ExpandedGraphCodeProof.countChildren, variablesAssemble]

theorem termVariables_computable : Computable Code.termVariables := by
  classical
  exact (LayeredComparison.FiniteGraph.Proof.exactDecreasingGraph Nat (List Nat)
    ExpandedGraphCodeProof.countChildren variablesAssemble id
    ExpandedGraphCodeProof.countChildren_primitive.to_comp variablesAssemble_primitive.to_comp
    Computable.id Code.termVariables ExpandedGraphCodeProof.countChildren_decreasing
    termVariables_equation).2
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
