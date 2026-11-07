module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalSquareRootArithmetic InternalSquareRootArithmeticSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalOriginalOrderSyntaxProof
open InternalOriginalOrderProof InternalQuotientComparisonProof InternalBetaTotalityProof
open InternalPositiveUnfoldingSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem leftWeakAdd (a b : OTerm α) :
    Nonempty (Derivation body Gamma (ltF a (suc (add a b)))) := by
  apply actualOriginalOrderIntroduction body α Gamma a (suc (add a b)) b
  rw [onEquality]
  exact ⟨addSucc a b⟩

theorem addStrictLeft (a s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF (add a s) (add a t))) := by
  apply orderCases Gamma s t _ h
  intro β j Delta w _ ⟨he⟩
  simp only [orderRename,addRelabel]
  apply actualOriginalOrderIntroduction body β Delta
    (add (a.relabel j) (s.relabel j)) (add (a.relabel j) (t.relabel j)) w
  rw [onEquality]
  exact ⟨trans (associativity (a.relabel j) (s.relabel j) (suc w))
    (congAddLeft (a.relabel j) he)⟩

/-- Original trichotomy supplies the weak reverse order; no natural semantics. -/
theorem notLessWeak (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y).not)) :
    Nonempty (Derivation body Gamma (ltF y (suc x))) := by
  obtain ⟨h⟩ := h
  obtain ⟨cmp⟩ := actualOriginalComparison body α x y
  have hc := compareView (weakenClosed cmp Gamma)
  have hl : Derivation body Gamma ((ltF x y).imp (ltF y (suc x))) :=
    Derivation.implicationIntroduction (Derivation.explosion
      (Derivation.implicationElimination (addHyp h _) (Derivation.hypothesis List.mem_cons_self)))
  have he : Derivation body Gamma ((eqn x y).imp (ltF y (suc x))) :=
    Derivation.implicationIntroduction (equalToNext (symm (Derivation.hypothesis List.mem_cons_self)))
  have hr : Nonempty (Derivation body (ltF y x :: Gamma) (ltF y (suc x))) :=
    rightSuccessor y x ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hr⟩ := hr
  have hrest : Derivation body Gamma ((eqn x y ⊔ ltF y x).imp (ltF y (suc x))) :=
    Derivation.implicationIntroduction (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp he _) (addHyp (Derivation.implicationIntroduction hr) _))
  exact ⟨disjunctionElimination hc hl hrest⟩

def intervalInputTransport (s : OTerm α) {n m : OTerm α}
    (he : Derivation body Gamma (eqn n m)) (h : Derivation body Gamma (interval s n)) :
    Derivation body Gamma (interval s m) := by
  have d := Derivation.equalityElimination (interval (s.relabel Sum.inl) (.var (.inr 0)))
    (emb n) (emb m) he
  simp only [intervalInstantiate,varBind,liftBind] at d
  exact d h

/-- The exact square interval for an arbitrary internally bounded offset. -/
theorem offsetInterval (s r : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF r (suc (add s s))))) :
    Nonempty (Derivation body Gamma (interval s (add (square s) r))) := by
  obtain ⟨lo⟩ := leftWeakAdd (body := body) (Gamma := Gamma) (square s) r
  obtain ⟨hi⟩ := addStrictLeft (square s) r (suc (add s s)) h
  exact ⟨Derivation.conjunctionIntroduction lo
    (orderRight (add (square s) r) (symm (successorSquareExpansion s)) hi)⟩

theorem lessPairInterval (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y))) :
    Nonempty (Derivation body Gamma (interval y (add (square y) x))) :=
  offsetInterval y x (strictTrans x y (suc (add y y)) h (leftWeakAdd y y))

theorem nonLessPairInterval (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF x y).not)) :
    Nonempty (Derivation body Gamma (interval x (add (add (square x) x) y))) := by
  obtain ⟨hh⟩ := addStrictLeft x y (suc x) (notLessWeak x y h)
  have hb : Nonempty (Derivation body Gamma (ltF (add x y) (suc (add x x)))) :=
    ⟨orderRight (add x y) (addSucc x x) hh⟩
  obtain ⟨hi⟩ := offsetInterval x (add x y) hb
  exact ⟨intervalInputTransport x (symm (associativity (square x) x y)) hi⟩

theorem notLessSum (x y : OTerm α) :
    Nonempty (Derivation body Gamma (ltF (add x y) x).not) := by
  let Delta := ltF (add x y) x :: Gamma
  have hc : Nonempty (Derivation body Delta (ltF (add x y) (add x y))) :=
    strictWeakTrans (add x y) x (add x y)
      ⟨Derivation.hypothesis List.mem_cons_self⟩ (leftWeakAdd x y)
  obtain ⟨hc⟩ := hc
  obtain ⟨irr⟩ := actualOriginalOrderIrreflexivity body α (add x y)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (weakenClosed irr Delta) hc)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairArithmeticProof
