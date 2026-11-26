module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedBooleanGraphForestProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeCalibrationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeProof
open BooleanGraphCode NonlinearProjectionCompletion

private theorem variables_step (payload tag : Nat) (h : tag < 10) :
    termVariables (10 * payload + tag) =
      if tag = 0 then [] else if tag = 1 then [payload]
      else if tag = 2 ∨ tag = 3 then termVariables payload.unpair.1 ++ termVariables payload.unpair.2
      else if tag = 4 ∨ tag = 5 then termVariables payload.unpair.2
      else termVariables payload := by
  have hm : (10 * payload + tag) % 10 = tag := by omega
  have hd : (10 * payload + tag) / 10 = payload := by omega
  rw [termVariables, hm, hd]

theorem literalTermVariables : BooleanGraphCodeTargets.LiteralTermVariables := by
  intro t
  induction t with
  | numeral n =>
    change termVariables (10 * n + 0) = []
    rw [variables_step n 0 (by decide)]; rfl
  | «variable» i =>
    rw [Term.encode, variables_step i 1 (by decide)]; rfl
  | add a b ha hb =>
    rw [Term.encode, variables_step _ 2 (by decide)]
    simpa only [reduceIte, Nat.unpair_pair, ha, hb] using (rfl : a.variables ++ b.variables = a.variables ++ b.variables)
  | subtract a b ha hb =>
    rw [Term.encode, variables_step _ 3 (by decide)]
    simpa only [reduceIte, Nat.unpair_pair, ha, hb] using (rfl : a.variables ++ b.variables = a.variables ++ b.variables)
  | multiply c a ha =>
    rw [Term.encode, variables_step _ 4 (by decide)]
    simpa only [reduceIte, Nat.unpair_pair, ha] using (rfl : a.variables = a.variables)
  | divide c a ha =>
    rw [Term.encode, variables_step _ 5 (by decide)]
    simpa only [reduceIte, Nat.unpair_pair, ha] using (rfl : a.variables = a.variables)
  | phi a ha =>
    rw [Term.encode, variables_step _ 6 (by decide)]
    simpa only [reduceIte, ha] using (rfl : a.variables = a.variables)
  | hyper a ha =>
    rw [Term.encode, variables_step _ 7 (by decide)]
    simpa only [reduceIte, ha] using (rfl : a.variables = a.variables)
  | phiInverse a ha =>
    rw [Term.encode, variables_step _ 8 (by decide)]
    simpa only [reduceIte, ha] using (rfl : a.variables = a.variables)
  | hyperInverse a ha =>
    rw [Term.encode, variables_step _ 9 (by decide)]
    simpa only [reduceIte, ha] using (rfl : a.variables = a.variables)

private theorem forest_step (payload tag : Nat) (h : tag < 8) :
    forest (8 * payload + tag) =
      if tag = 0 ∨ tag = 1 then 0
      else if tag = 2 ∨ tag = 3 then WindowCode.add payload.unpair.1 payload.unpair.2
      else if tag = 4 then payload.unpair.2
      else if tag = 5 then forest payload
      else WindowCode.add (forest payload.unpair.1) (forest payload.unpair.2) := by
  have hm : (8 * payload + tag) % 8 = tag := by omega
  have hd : (8 * payload + tag) / 8 = payload := by omega
  rw [forest, hm, hd]

theorem literalForest : BooleanGraphCodeTargets.LiteralForest := by
  intro p
  induction p with
  | truth => change forest (8 * 0 + 0) = 0; rw [forest_step 0 0 (by decide)]; rfl
  | falsity => change forest (8 * 0 + 1) = 0; rw [forest_step 0 1 (by decide)]; rfl
  | equal a b => rw [Matrix.encode, forest_step _ 2 (by decide)]; simp [WindowCode.add, ExpandedBooleanGraph.forest, Term.encode]
  | less a b => rw [Matrix.encode, forest_step _ 3 (by decide)]; simp [WindowCode.add, ExpandedBooleanGraph.forest, Term.encode]
  | divisible m a => rw [Matrix.encode, forest_step _ 4 (by decide)]; simp [ExpandedBooleanGraph.forest]
  | negative p hp => rw [Matrix.encode, forest_step _ 5 (by decide)]; simpa only [reduceIte] using hp
  | conjunction p q hp hq =>
    rw [Matrix.encode, forest_step _ 6 (by decide)]
    simp [hp, hq, WindowCode.add, ExpandedBooleanGraph.forest, Term.encode]
  | disjunction p q hp hq =>
    rw [Matrix.encode, forest_step _ 7 (by decide)]
    simp [hp, hq, WindowCode.add, ExpandedBooleanGraph.forest, Term.encode]

private theorem predicate_step (start payload tag : Nat) (h : tag < 8) :
    predicate start (8 * payload + tag) =
      if tag = 0 then 0 else if tag = 1 then 1
      else if tag = 2 ∨ tag = 3 then
        SourceRows.Code.relation (tag == 3)
          (ExpandedGraphCode.output start payload.unpair.1)
          (ExpandedGraphCode.output (start + ExpandedGraphCode.nodeCount payload.unpair.1) payload.unpair.2)
      else if tag = 4 then
        let m := payload.unpair.1
        let x := ExpandedGraphCode.output start payload.unpair.2
        if m = 0 then SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData x)])
        else 6 * Encodable.encode ((1, m - 1, (0 : Int), [(1 : Int, SourceTermGraph.Code.variableData x)]) : NormalForm.Code.AtomData) + 2
      else if tag = 5 then 6 * predicate start payload + 3
      else 6 * Nat.pair (predicate start payload.unpair.1)
        (predicate (start + ExpandedGraphCode.nodeCount (forest payload.unpair.1)) payload.unpair.2) + (tag - 2) := by
  have hm : (8 * payload + tag) % 8 = tag := by omega
  have hd : (8 * payload + tag) / 8 = payload := by omega
  rw [predicate, hm, hd]

theorem literalPredicate : BooleanGraphCodeTargets.LiteralPredicate := by
  intro start p
  induction p generalizing start with
  | truth => change predicate start (8 * 0 + 0) = 0; rw [predicate_step start 0 0 (by decide)]; rfl
  | falsity => change predicate start (8 * 0 + 1) = 1; rw [predicate_step start 0 1 (by decide)]; rfl
  | equal a b =>
    rw [Matrix.encode, predicate_step _ _ 2 (by decide)]
    simp only [reduceIte, Nat.unpair_pair]
    rw [(ExpandedGraphCodeProof.literalAllocation start a).2,
      ExpandedGraphCodeProof.literalNodeCount a,
      (ExpandedGraphCodeProof.literalAllocation (start + ExpandedGraph.nodeCount a) b).2]
    exact SourceRowsCodeProof.relation_calibration false _ _
  | less a b =>
    rw [Matrix.encode, predicate_step _ _ 3 (by decide)]
    simp only [reduceIte, Nat.unpair_pair]
    rw [(ExpandedGraphCodeProof.literalAllocation start a).2,
      ExpandedGraphCodeProof.literalNodeCount a,
      (ExpandedGraphCodeProof.literalAllocation (start + ExpandedGraph.nodeCount a) b).2]
    exact SourceRowsCodeProof.relation_calibration true _ _
  | divisible m a =>
    rw [Matrix.encode, predicate_step _ _ 4 (by decide)]
    simp only [reduceIte, Nat.unpair_pair]
    rw [(ExpandedGraphCodeProof.literalAllocation start a).2]
    by_cases hm : m = 0
    · simp only [hm, reduceIte, ExpandedBooleanGraph.predicate]
      exact SourceTermGraphCodeProof.equation_calibration _
    · simp only [hm, reduceIte, ExpandedBooleanGraph.predicate]
      rfl
  | negative p hp =>
    rw [Matrix.encode, predicate_step _ _ 5 (by decide)]
    simpa only [reduceIte, ExpandedBooleanGraph.predicate, NormalForm.Formula.encode] using congrArg (fun n => 6 * n + 3) (hp start)
  | conjunction p q hp hq =>
    rw [Matrix.encode, predicate_step _ _ 6 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, literalForest,
      ExpandedGraphCodeProof.literalNodeCount, hp, hq]
    rfl
  | disjunction p q hp hq =>
    rw [Matrix.encode, predicate_step _ _ 7 (by decide)]
    simp only [reduceIte, Nat.unpair_pair, literalForest,
      ExpandedGraphCodeProof.literalNodeCount, hp, hq]
    rfl

theorem literalFreshAllocation : BooleanGraphCodeTargets.LiteralFreshAllocation := by
  intro bound p
  have hs : startFor bound p.encode = ExpandedBooleanGraph.startFor bound p := by
    simp only [startFor, literalForest, literalTermVariables,
      ExpandedBooleanGraphProof.literalForestSupport, ExpandedBooleanGraph.startFor]
  refine ⟨hs, ?_⟩
  simp only [allocated, hs, literalForest,
    (ExpandedGraphCodeProof.literalAllocation _ _).1, ExpandedBooleanGraph.allocated]

theorem literalCompiler : BooleanGraphCodeTargets.LiteralCompiler := by
  intro bound p
  simp only [compile, literalForest, (literalFreshAllocation bound p).1,
    ExpandedGraphCodeProof.literalGraphCalibration, literalPredicate]
  rfl

#print axioms literalTermVariables
#print axioms literalForest
#print axioms literalPredicate
#print axioms literalFreshAllocation
#print axioms literalCompiler
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeProof
