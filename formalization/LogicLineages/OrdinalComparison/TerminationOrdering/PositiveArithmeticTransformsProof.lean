module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticTransforms PositiveArithmeticOperatorsSupportProof

theorem relabelTruth {α : Type} (phi : Positive α) : ∀ (β : Type) (g : α → β) (P : Nat → Prop) (v : β → Nat),
    realize P (relabel g phi).formula v ↔ realize P phi.formula (v ∘ g) := by
  induction phi with
  | arithmetic a =>
    intro β g P v
    change realize P (arithmeticEmbedding.onFormula (a.relabel g)) v ↔ realize P (arithmeticEmbedding.onFormula a) (v ∘ g)
    rw [embeddingTruth,embeddingTruth]
    exact Formula.realize_relabel
  | predicate t =>
    intro β g P v
    change realize P (Positive.predicate (t.relabel g)).formula v ↔ realize P (Positive.predicate t).formula (v ∘ g)
    rw [predicateTruth,predicateTruth,Term.realize_relabel]
  | conj p q ihp ihq =>
    intro β g P v
    change realize P (Positive.conj (relabel g p) (relabel g q)).formula v ↔ _
    rw [conjTruth,conjTruth,ihp,ihq]
  | guarded guard p ih =>
    intro β g P v
    change realize P (Positive.guarded (guard.relabel g) (relabel g p)).formula v ↔ _
    rw [guardedTruth,guardedTruth,ih]
    exact imp_congr Formula.realize_relabel Iff.rfl
  | all p ih =>
    intro β g P v
    change realize P (Positive.all (relabel (Sum.map g id) p)).formula v ↔ _
    rw [allTruth,allTruth]
    apply forall_congr'
    intro xs
    rw [ih]
    have hv : (Sum.elim v xs) ∘ Sum.map g id = Sum.elim (v ∘ g) xs := by
      funext x
      cases x <;> rfl
    rw [hv]

theorem positiveRelabelTruth : PositiveArithmeticTransformsTargets.ActualPositiveRelabelTruth := by
  intro α β g phi P v
  exact relabelTruth phi β g P v

theorem tagTermTruth {α : Type} (odd : Bool) (t : OrdinaryArithmetic.Term α) (v : α → Nat) :
    (tagTerm odd t).realize v = tagNumber odd (t.realize v) := by
  cases odd <;> rfl

theorem positiveTagTruth : PositiveArithmeticTransformsTargets.ActualPositiveTagTruth := by
  intro α odd phi P v
  induction phi with
  | arithmetic a =>
    change realize P (arithmeticEmbedding.onFormula a) v ↔ realize (fun x => P (tagNumber odd x)) (arithmeticEmbedding.onFormula a) v
    rw [embeddingTruth,embeddingTruth]
  | predicate t =>
    change realize P (Positive.predicate (tagTerm odd t)).formula v ↔ _
    rw [predicateTruth,predicateTruth,tagTermTruth]
  | conj p q ihp ihq =>
    change realize P (Positive.conj (tagPredicate odd p) (tagPredicate odd q)).formula v ↔ _
    rw [conjTruth,conjTruth,ihp,ihq]
  | guarded guard p ih =>
    change realize P (Positive.guarded guard (tagPredicate odd p)).formula v ↔ _
    rw [guardedTruth,guardedTruth,ih]
  | all p ih =>
    change realize P (Positive.all (tagPredicate odd p)).formula v ↔ _
    rw [allTruth,allTruth]
    exact forall_congr' (fun xs => ih (Sum.elim v xs))

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsProof
