module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsProof
open FirstOrder Language PositiveArithmeticOperators PositiveArithmeticOperatorsSupportProof

theorem arithmeticEmbeddingTruth : PositiveArithmeticOperatorsTargets.ActualArithmeticEmbeddingTruth := embeddingTruth

theorem positiveMonotonicity : PositiveArithmeticOperatorsTargets.ActualPositiveMonotonicity := by
  intro α phi P Q hpq
  induction phi with
  | arithmetic a =>
    intro v h
    exact (embeddingTruth _ a Q v).mpr ((embeddingTruth _ a P v).mp h)
  | predicate t =>
    intro v h
    exact (predicateTruth Q t v).mpr (hpq _ ((predicateTruth P t v).mp h))
  | conj p q ihp ihq =>
    intro v h
    have hh := (conjTruth P p q v).mp h
    exact (conjTruth Q p q v).mpr ⟨ihp v hh.1,ihq v hh.2⟩
  | guarded g p ih =>
    intro v h
    exact (guardedTruth Q g p v).mpr (fun hg => ih v ((guardedTruth P g p v).mp h hg))
  | all p ih =>
    intro v h
    exact (allTruth Q p v).mpr (fun xs => ih _ ((allTruth P p v).mp h xs))

theorem accessibilityOperatorTruth : PositiveArithmeticOperatorsTargets.ActualAccessibilityOperatorTruth := by
  intro carrier edge P context x
  rw [accessibilityOperator,conjTruth,allTruth]
  change (realize P (arithmeticEmbedding.onFormula carrier) ![context,x] ∧ _) ↔ _
  rw [embeddingTruth]
  have hedge (xs : Fin 1 → Nat) :
      Formula.Realize (edge.subst ![.var (.inl 0),.var (.inl 1),.var (.inr (0 : Fin 1))]) (Sum.elim ![context,x] xs) ↔
        edge.Realize ![context,x,xs 0] := by
    simp only [Formula.Realize]
    rw [BoundedFormula.realize_subst]
    have hv : (fun i : Fin 3 =>
        (![(.var (.inl 0) : OrdinaryArithmetic.Term (Fin 2 ⊕ Fin 1)),.var (.inl 1),.var (.inr (0 : Fin 1))] i).realize
          (Sum.elim ![context,x] xs)) = ![context,x,xs 0] := by
      funext i
      exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) j) i
    rw [hv]
  simp only [guardedTruth,predicateTruth,hedge,Term.realize_var,Sum.elim_inr]
  constructor
  · rintro ⟨hc,h⟩
    refine ⟨hc,?_⟩
    intro y he
    exact h (fun _ => y) he
  · rintro ⟨hc,h⟩
    refine ⟨hc,?_⟩
    intro xs he
    exact h (xs 0) he

theorem sourcePositiveOperators : PositiveArithmeticOperatorsTargets.ActualSourcePositiveOperators := by
  intro n arity Gamma
  obtain ⟨scalar,list,hc⟩ := OrdinaryArithmeticCarrierProof.encodedCarrierFormulas n arity Gamma
  obtain ⟨pH,pR,_,_,_,hR⟩ := OrdinaryArithmeticQuotientProof.encodedHAndPositiveR n arity Gamma
  obtain ⟨pD,_,hD⟩ := OrdinaryArithmeticDirectProof.encodedDirectFormula n arity Gamma
  refine ⟨accessibilityOperator scalar (OrdinaryArithmeticQuotient.certificateGraph pR),
    accessibilityOperator list (OrdinaryArithmeticQuotient.certificateGraph pD),?_⟩
  intro P context x
  constructor
  · rw [accessibilityOperatorTruth,(hc context x).1]
    exact and_congr Iff.rfl (forall_congr' (fun y => imp_congr (hR context x y) Iff.rfl))
  · rw [accessibilityOperatorTruth,(hc context x).2]
    exact and_congr Iff.rfl (forall_congr' (fun y => imp_congr (hD context x y) Iff.rfl))

end LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticOperatorsProof
