module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionWorkingTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundProjectionCodeStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
open SourceDecision NonlinearProjectionCompletion CommonLayerSyntax
attribute [local irreducible] Nat.sqrt Nat.unpair embedTerm eliminate binder

private theorem embedding_step (payload tag : Nat) (h : tag < 4) :
    embedTerm (4 * payload + tag) =
      if tag = 0 then 10 * payload else if tag = 1 then 10 * payload + 1
      else if tag = 2 then WindowCode.add (embedTerm payload.unpair.1) (embedTerm payload.unpair.2)
      else WindowCode.phi (embedTerm payload) := by
  have hm : (4 * payload + tag) % 4 = tag := by omega
  have hd : (4 * payload + tag) / 4 = payload := by omega
  rw [embedTerm, hm, hd]

theorem literalTermEmbedding : SourceDecisionTargets.LiteralTermEmbedding := by
  intro t
  induction t with
  | numeral n =>
    change embedTerm (4 * n + 0) = 10 * n
    rw [embedding_step _ 0 (by decide)]; rfl
  | «variable» i =>
    rw [BaseTerm.encode, embedding_step _ 1 (by decide)]; rfl
  | add a b ha hb =>
    rw [BaseTerm.encode, embedding_step _ 2 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair, ha, hb]
    rfl
  | phi a ha =>
    rw [BaseTerm.encode, embedding_step _ 3 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, ha]
    rfl

theorem literalBinderCompiler : SourceDecisionTargets.LiteralBinderCompiler := by
  intro i p
  unfold binder
  rw [(BooleanGraphCodeProof.literalFreshAllocation [i] p).2,
    BooleanGraphCodeProof.literalCompiler [i] p,
    WholeBoundProjectionCodeProof.literalInitializedProjection
      (i :: ExpandedBooleanGraph.allocated [i] p) (ExpandedBooleanGraph.compile [i] p)]
  rfl

private theorem compiler_step (payload tag : Nat) (h : tag < 5) :
    eliminate (5 * payload + tag) =
      if tag = 0 then (8 * Nat.pair (embedTerm payload.unpair.1) (embedTerm payload.unpair.2) + 2)
      else if tag = 1 then WindowCode.less (embedTerm payload.unpair.1) (embedTerm payload.unpair.2)
      else if tag = 2 then WindowCode.negative (eliminate payload)
      else if tag = 3 then WindowCode.conjunction (eliminate payload.unpair.1) (eliminate payload.unpair.2)
      else binder payload.unpair.1 (eliminate payload.unpair.2) := by
  have hm : (5 * payload + tag) % 5 = tag := by omega
  have hd : (5 * payload + tag) / 5 = payload := by omega
  rw [eliminate, hm, hd]

theorem literalSourceCompiler : SourceDecisionTargets.LiteralSourceCompiler := by
  intro p
  induction p with
  | equal a b =>
    change eliminate (5 * Nat.pair a.encode b.encode + 0) = _
    rw [compiler_step _ 0 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair]
    rw [literalTermEmbedding a, literalTermEmbedding b]
    rfl
  | less a b =>
    rw [SourceFormula.encode, compiler_step _ 1 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair]
    rw [literalTermEmbedding a, literalTermEmbedding b]
    rfl
  | negative p hp =>
    rw [SourceFormula.encode, compiler_step _ 2 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, hp]
    rfl
  | conjunction p q hp hq =>
    rw [SourceFormula.encode, compiler_step _ 3 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair, hp, hq]
    rfl
  | existsNat i p hp =>
    rw [SourceFormula.encode, compiler_step _ 4 (by decide)]
    simp only [Nat.reduceEqDiff, ↓reduceIte, Nat.unpair_pair, hp]
    exact literalBinderCompiler i _

#print axioms literalTermEmbedding
#print axioms literalBinderCompiler
#print axioms literalSourceCompiler
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.SourceDecisionProof
