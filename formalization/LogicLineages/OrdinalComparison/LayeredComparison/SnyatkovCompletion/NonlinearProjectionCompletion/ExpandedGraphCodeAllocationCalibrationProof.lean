module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
theorem count_step (n tag : Nat) (ht : tag < 10) :
    nodeCount (10 * n + tag) =
      if tag = 0 then 1
      else if tag = 1 then 1
      else if tag = 2 then nodeCount n.unpair.1 + nodeCount n.unpair.2 + 1
      else if tag = 3 then nodeCount n.unpair.1 + nodeCount n.unpair.2 + 1
      else if tag = 4 then nodeCount n.unpair.2 + 1
      else if tag = 5 then nodeCount n.unpair.2 + 1
      else if tag = 8 then nodeCount n + 2
      else nodeCount n + 1 := by
  have hm : (10 * n + tag) % 10 = tag := by omega
  have hd : (10 * n + tag) / 10 = n := by omega
  rw [nodeCount, hm, hd]
#print axioms count_step

theorem nodeCount_calibration (t : Term) : nodeCount t.encode = ExpandedGraph.nodeCount t := by
  induction t with
  | numeral n =>
      simpa only [Term.encode, Nat.add_zero, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair] using count_step n 0 (by decide)
  | «variable» i =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair] using count_step i 1 (by decide)
  | add a b ha hb =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha, hb] using count_step (Nat.pair a.encode b.encode) 2 (by decide)
  | subtract a b ha hb =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha, hb] using count_step (Nat.pair a.encode b.encode) 3 (by decide)
  | multiply c a ha =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha] using count_step (Nat.pair c a.encode) 4 (by decide)
  | divide c a ha =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha] using count_step (Nat.pair c a.encode) 5 (by decide)
  | phi a ha =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha] using count_step a.encode 6 (by decide)
  | hyper a ha =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha] using count_step a.encode 7 (by decide)
  | phiInverse a ha =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha] using count_step a.encode 8 (by decide)
  | hyperInverse a ha =>
      simpa only [Term.encode, ExpandedGraph.nodeCount, Nat.reduceEqDiff,
        ↓reduceIte, Nat.unpair_pair, ha] using count_step a.encode 9 (by decide)
#print axioms nodeCount_calibration

theorem literalNodeCount : ExpandedGraphCodeTargets.LiteralNodeCount := nodeCount_calibration
#print axioms literalNodeCount

theorem output_calibration (start : Nat) (t : Term) :
    output start t.encode = ExpandedGraph.output start t := by
  unfold output ExpandedGraph.output
  rw [nodeCount_calibration]
#print axioms output_calibration

theorem literalAllocation : ExpandedGraphCodeTargets.LiteralAllocation := by
  intro start t
  constructor
  · unfold allocated ExpandedGraph.allocated
    rw [nodeCount_calibration]
  · exact output_calibration start t
#print axioms literalAllocation


end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
