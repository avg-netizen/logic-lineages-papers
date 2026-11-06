module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalBetaWitness InternalBetaWitnessProof InternalBetaDivisionProof InternalBetaDivisionSyntaxProof
open InternalQuotientComparisonProof InternalQuotientGapProof InternalQuotientComparison
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalAdditionLawsProof
open InternalAdditionCancellationProof InternalMultiplicationLawsProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type}

theorem excludeSmallerQuotient (Gamma : List (Formula α)) (a M q q' r s d : OrdinaryArithmetic.Term α)
    (ha : Derivation body Gamma (eqn a (add (mul q M) r)))
    (hb : Derivation body Gamma (eqn a (add (mul q' M) s)))
    (hr : Derivation body Gamma (eqn (add r (suc d)) M)) :
    Nonempty (Derivation body Gamma (ltF q q').not) := by
  have h : Nonempty (Derivation body (ltF q q' :: Gamma) (⊥ : Formula α)) := by
    apply orderCases (ltF q q' :: Gamma) q q' _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta w hi ⟨gap⟩
    have ha' := renameInto ⟨addHyp ha (ltF q q')⟩ j Delta hi
    have hb' := renameInto ⟨addHyp hb (ltF q q')⟩ j Delta hi
    have hr' := renameInto ⟨addHyp hr (ltF q q')⟩ j Delta hi
    simp only [eqnRelabel,addRelabel,mulRelabel,sucRelabel] at ha' hb' hr'
    obtain ⟨ha'⟩ := ha'
    obtain ⟨hb'⟩ := hb'
    obtain ⟨hr'⟩ := hr'
    exact ⟨gapContradiction (a.relabel j) (M.relabel j) (q.relabel j) (q'.relabel j)
      (r.relabel j) (s.relabel j) (d.relabel j) w ha' hb' hr' gap⟩
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

theorem remainderUnique (Gamma : List (Formula α)) (a M q q' r s d e : OrdinaryArithmetic.Term α)
    (ha : Derivation body Gamma (eqn a (add (mul q M) r)))
    (hb : Derivation body Gamma (eqn a (add (mul q' M) s)))
    (hr : Derivation body Gamma (eqn (add r (suc d)) M))
    (hs : Derivation body Gamma (eqn (add s (suc e)) M)) :
    Nonempty (Derivation body Gamma (eqn r s)) := by
  obtain ⟨notLess⟩ := excludeSmallerQuotient Gamma a M q q' r s d ha hb hr
  obtain ⟨notGreater⟩ := excludeSmallerQuotient Gamma a M q' q s r e hb ha hs
  obtain ⟨cmp⟩ := actualOriginalComparison body α q q'
  have hc := compareView (weakenClosed cmp Gamma)
  have hp : Derivation body Gamma ((ltF q q').imp (eqn r s)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp notLess (ltF q q'))
        (Derivation.hypothesis List.mem_cons_self)))
  have hq : Derivation body Gamma ((eqn q q').imp (eqn r s)) := by
    apply Derivation.implicationIntroduction
    apply Derivation.implicationElimination (InternalAdditionCancellationProof.leftCancellation r s (mul q M))
    exact trans (symm (addHyp ha (eqn q q')))
      (trans (addHyp hb (eqn q q'))
        (InternalMultiplicationLawsProof.congAddRight s
          (symm (congMulRight M (Derivation.hypothesis List.mem_cons_self)))))
  have hn : Derivation body Gamma ((ltF q' q).imp (eqn r s)) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp notGreater (ltF q' q))
        (Derivation.hypothesis List.mem_cons_self)))
  have hqn : Derivation body Gamma ((eqn q q' ⊔ ltF q' q).imp (eqn r s)) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp hq _) (addHyp hn _))
  exact ⟨disjunctionElimination hc hp hqn⟩

theorem actualOriginalBetaUniqueness : InternalBetaUniquenessTargets.ActualOriginalBetaUniqueness := by
  intro body α a b i r s
  let Gamma := [betaF a b i r ⊓ betaF a b i s]
  have hb1 : Nonempty (Derivation body Gamma (betaF a b i r)) :=
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
  have hb2 : Nonempty (Derivation body Gamma (betaF a b i s)) :=
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  have h : Nonempty (Derivation body Gamma (eqn r s)) := by
    apply betaCases Gamma a b i r _ hb1
    intro β j Delta q d hi ⟨er⟩
    rw [eqnRelabel]
    rw [equationEmbedding] at er
    have second := renameInto hb2 j Delta hi
    change Nonempty (Derivation body Delta ((arithmeticEmbedding.onFormula
      (OrdinaryArithmetic.betaFormula a b i s)).relabel j)) at second
    rw [betaRename] at second
    apply betaCases Delta (a.relabel j) (b.relabel j) (i.relabel j) (s.relabel j) _ second
    intro γ l Theta q' e hl ⟨es⟩
    rw [eqnRelabel]
    rw [equationEmbedding] at es
    have eqr := renameInto ⟨Derivation.conjunctionLeft er⟩ l Theta hl
    have boundr := renameInto ⟨Derivation.conjunctionRight er⟩ l Theta hl
    simp only [eqnRelabel,addRelabel,mulRelabel,modulusRename,sucRelabel] at eqr boundr
    obtain ⟨eqr⟩ := eqr
    obtain ⟨boundr⟩ := boundr
    exact remainderUnique Theta ((a.relabel j).relabel l)
      (modulus ((b.relabel j).relabel l) ((i.relabel j).relabel l))
      (q.relabel l) q' ((r.relabel j).relabel l) ((s.relabel j).relabel l) (d.relabel l) e
      eqr (Derivation.conjunctionLeft es) boundr (Derivation.conjunctionRight es)
  obtain ⟨h⟩ := h
  change Nonempty (Derivation body []
    ((betaF a b i r ⊓ betaF a b i s).imp (arithmeticEmbedding.onFormula (r.equal s))))
  rw [onEquality]
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaUniquenessProof
