module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeAllocationProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
abbrev GraphCall := Nat × Nat

/-- Actual recursive calls. Right-child starts change by the computed count
of the complete left subtree; all calls retain their exact code measure. -/
def graphChildren (p : GraphCall) : List GraphCall :=
  if p.2 % 10 = 0 ∨ p.2 % 10 = 1 then []
  else if p.2 % 10 = 2 ∨ p.2 % 10 = 3 then
    [(p.1, (p.2 / 10).unpair.1),
      (p.1 + nodeCount (p.2 / 10).unpair.1, (p.2 / 10).unpair.2)]
  else if p.2 % 10 = 4 ∨ p.2 % 10 = 5 then [(p.1, (p.2 / 10).unpair.2)]
  else if p.2 % 10 = 6 ∨ p.2 % 10 = 8 then [(p.1, p.2 / 10)]
  else []

def graphAssemble (p : GraphCall) (values : List Nat) : Nat :=
  let start := p.1
  let code := p.2
  if code % 10 = 0 then SourceTermGraph.Code.equation (SourceTermGraph.Code.numeralRow start (code / 10))
  else if code % 10 = 1 then SourceTermGraph.Code.equation (SourceTermGraph.Code.variableRow start (code / 10))
  else if code % 10 = 2 then
    let a := (code / 10).unpair.1
    let b := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (values.getD 0 0)
      (SourceTermGraph.Code.conjunction (values.getD 1 0)
        (SourceTermGraph.Code.equation (SourceTermGraph.Code.additionRow (output start code)
          (output start a) (output (start + nodeCount a) b))))
  else if code % 10 = 3 then
    let a := (code / 10).unpair.1
    let b := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (values.getD 0 0)
      (SourceTermGraph.Code.conjunction (values.getD 1 0)
        (subtraction (output start code) (output start a) (output (start + nodeCount a) b)))
  else if code % 10 = 4 then
    let a := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (values.getD 0 0)
      (SourceTermGraph.Code.equation (multiplyRow (output start code) (output start a) (code / 10).unpair.1))
  else if code % 10 = 5 then
    let a := (code / 10).unpair.2
    SourceTermGraph.Code.conjunction (values.getD 0 0)
      (division (output start code) (output start a) (code / 10).unpair.1)
  else if code % 10 = 6 then
    SourceTermGraph.Code.conjunction (values.getD 0 0)
      (SourceTermGraph.Code.equation (SourceTermGraph.Code.phiRow (output start code) (output start (code / 10))))
  else if code % 10 = 8 then
    SourceTermGraph.Code.conjunction (values.getD 0 0)
      (inverse (start + nodeCount (code / 10)) (output start code) (output start (code / 10)))
  else 1

theorem graphChildren_decreasing : ∀ p q : GraphCall,
    q ∈ graphChildren p → q.2 < p.2 := by
  intro p q h
  by_cases hleaf : p.2 % 10 = 0 ∨ p.2 % 10 = 1
  · simp [graphChildren, hleaf] at h
  have hpos : 0 < p.2 := by omega
  have hd : p.2 / 10 < p.2 := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (p.2 / 10)
  have hr := Nat.unpair_right_le (p.2 / 10)
  rcases q with ⟨start, code⟩
  unfold graphChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  all_goals omega
#print axioms graphChildren_decreasing

theorem graph_equation (p : GraphCall) :
    graph p.1 p.2 = graphAssemble p ((graphChildren p).map (fun q => graph q.1 q.2)) := by
  rcases p with ⟨start, code⟩
  rw [graph]
  split_ifs <;> simp_all [graphChildren, graphAssemble]
#print axioms graph_equation


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
