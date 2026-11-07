module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientGapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open SourceComputabilityFormulaSupportProof InternalSquareRootArithmetic
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalSourceInversionSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalMultiplicationLeftSuccessorProof
open InternalQuotientGapProof InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalQuotientComparisonSyntaxProof InternalQuotientComparisonProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof InternalBetaDivisionSyntaxProof
open InternalLeastNumberProof InternalBetaBoundaryProof

@[simp] theorem intervalRename {α β : Type} (s n : OTerm α) (j : α → β) :
    (interval s n).relabel j = interval (s.relabel j) (n.relabel j) := by
  change (ltF (square s) (suc n)).relabel j ⊓
    (ltF n (square (suc s))).relabel j = _
  simp only [orderRename,square,mulRelabel,sucRelabel]
  rfl

@[simp] theorem intervalSubst {α β : Type} (s n : OTerm α) (ts : α → OTerm β) :
    (interval s n).subst (fun a => emb (ts a)) = interval (s.subst ts) (n.subst ts) := by
  change (ltF (square s) (suc n)).subst (fun a => emb (ts a)) ⊓
    (ltF n (square (suc s))).subst (fun a => emb (ts a)) = _
  simp only [orderSubst,square,mulSubst,sucSubst]
  rfl

@[simp] theorem intervalInstantiate {α : Type} (s n : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (interval s n) (emb t) = interval (s.subst (bindTerm t)) (n.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,intervalSubst]

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def squareCongr {s t : OTerm α} (h : Derivation body Gamma (eqn s t)) :
    Derivation body Gamma (eqn (square s) (square t)) :=
  trans (congMulRight s h) (congMulLeft t h)

def orderLeft {s t : OTerm α} (u : OTerm α) (he : Derivation body Gamma (eqn s t))
    (h : Derivation body Gamma (ltF s u)) : Derivation body Gamma (ltF t u) := by
  have d := Derivation.equalityElimination (ltF (.var (.inr 0)) (u.relabel Sum.inl))
    (emb s) (emb t) he
  simp only [orderInstantiate,varBind,liftBind] at d
  exact d h

def orderRight (s : OTerm α) {t u : OTerm α} (he : Derivation body Gamma (eqn t u))
    (h : Derivation body Gamma (ltF s t)) : Derivation body Gamma (ltF s u) := by
  have d := Derivation.equalityElimination (ltF (s.relabel Sum.inl) (.var (.inr 0)))
    (emb t) (emb u) he
  simp only [orderInstantiate,varBind,liftBind] at d
  exact d h

def intervalOutputTransport (n : OTerm α) {s t : OTerm α}
    (he : Derivation body Gamma (eqn s t)) (h : Derivation body Gamma (interval s n)) :
    Derivation body Gamma (interval t n) := by
  have d := Derivation.equalityElimination (interval (.var (.inr 0)) (n.relabel Sum.inl))
    (emb s) (emb t) he
  simp only [intervalInstantiate,varBind,liftBind] at d
  exact d h

/-- Literal PA multiplication and addition equations, without evaluation. -/
def successorSquareExpansion (s : OTerm α) :
    Derivation body Gamma (eqn (square (suc s)) (add (square s) (suc (add s s)))) :=
  trans (leftSuccessorMultiplication s (suc s))
    (trans (InternalMultiplicationLawsProof.congAddRight (suc s) (mulSucc s s))
      (trans (associativity (square s) s (suc s))
        (congAddLeft (square s) (addSucc s s))))

def successorSquareStrict (s : OTerm α) :
    Derivation body Gamma (ltF (square s) (square (suc s))) := by
  rw [embedding]
  apply Derivation.existentialIntroduction (emb (add s s))
  rw [witnessInstantiate]
  exact symm (successorSquareExpansion s)

/-- The sum-of-two-terms expansion uses only original distributivity. -/
def squareAddExpansion (s t : OTerm α) :
    Derivation body Gamma (eqn (square (add s t))
      (add (square s) (add (mul s t) (mul t (add s t))))) := by
  let x := add s t
  have h1 : Derivation body Gamma (eqn (square x) (add (mul s x) (mul t x))) :=
    leftDistributivity s t x
  have h2 : Derivation body Gamma (eqn (add (mul s x) (mul t x))
      (add (add (square s) (mul s t)) (mul t x))) :=
    InternalMultiplicationLawsProof.congAddRight (mul t x) (distributivity s s t)
  exact trans h1 (trans h2 (associativity (square s) (mul s t) (mul t x)))

/-- A concrete arithmetic term for the positive square-gap witness. -/
def squareGap (s d : OTerm α) : OTerm α :=
  add (mul s (suc d)) (add (mul d (add s (suc d))) (add s d))

def squareGapPositive (s d : OTerm α) :
    Derivation body Gamma (eqn (add (mul s (suc d)) (mul (suc d) (add s (suc d))))
      (suc (squareGap s d))) := by
  let x := add s (suc d)
  let a := mul s (suc d)
  let b := mul d x
  let c := add s d
  have h1 : Derivation body Gamma (eqn (add a (mul (suc d) x)) (add a (add b x))) :=
    congAddLeft a (leftSuccessorMultiplication d x)
  have h2 : Derivation body Gamma (eqn (add a (add b x)) (add a (add b (suc c)))) :=
    congAddLeft a (congAddLeft b (addSucc s d))
  have h3 : Derivation body Gamma (eqn (add a (add b (suc c))) (add a (suc (add b c)))) :=
    congAddLeft a (addSucc b c)
  exact trans h1 (trans h2 (trans h3 (addSucc a (add b c))))

/-- Explicit positive gap in the square of s+succ(d). -/
def squareGapExpansion (s d : OTerm α) :
    Derivation body Gamma (eqn (square (add s (suc d)))
      (add (square s) (suc (squareGap s d)))) :=
  trans (squareAddExpansion s (suc d)) (congAddLeft (square s) (squareGapPositive s d))

theorem squareStrictMonotonicity (s t : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF (square s) (square t))) := by
  apply orderCases Gamma s t _ h
  intro β j Delta d _ ⟨he⟩
  simp only [orderRename,square,mulRelabel]
  apply actualOriginalOrderIntroduction body β Delta
    (square (s.relabel j)) (square (t.relabel j))
    (squareGap (s.relabel j) d)
  rw [onEquality]
  exact ⟨trans (symm (squareGapExpansion (s.relabel j) d)) (squareCongr he)⟩

theorem strictTrans (s t u : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF s t)))
    (k : Nonempty (Derivation body Gamma (ltF t u))) :
    Nonempty (Derivation body Gamma (ltF s u)) := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  obtain ⟨d⟩ := actualOriginalOrderTransitivity body α s t u
  exact ⟨Derivation.implicationElimination (weakenClosed d Gamma) (Derivation.conjunctionIntroduction h k)⟩

theorem rightSuccessor (s t : OTerm α) (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF s (suc t))) := by
  obtain ⟨h⟩ := h
  obtain ⟨d⟩ := actualRightSuccessorOrder body α s t
  exact ⟨Derivation.implicationElimination (weakenClosed d Gamma) h⟩

/-- Strict/weak transitivity derives from the existing original PA split. -/
theorem strictWeakTrans (s t u : OTerm α)
    (h : Nonempty (Derivation body Gamma (ltF s t)))
    (k : Nonempty (Derivation body Gamma (ltF t (suc u)))) :
    Nonempty (Derivation body Gamma (ltF s u)) := by
  obtain ⟨h⟩ := h
  obtain ⟨k⟩ := k
  obtain ⟨split⟩ := actualRightSuccessorSplit body α t u
  rw [onEquality] at split
  have hd := Derivation.implicationElimination (weakenClosed split Gamma) k
  have hl : Nonempty (Derivation body (ltF t u :: Gamma) (ltF s u)) :=
    strictTrans s t u ⟨addHyp h _⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hl⟩ := hl
  have he : Derivation body (eqn t u :: Gamma) (ltF s u) :=
    orderRight s (Derivation.hypothesis List.mem_cons_self) (addHyp h _)
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction he)⟩

/-- If s<t, the next square after s is no greater than t squared. -/
theorem nextSquareWeak (s t : OTerm α) (h : Nonempty (Derivation body Gamma (ltF s t))) :
    Nonempty (Derivation body Gamma (ltF (square (suc s)) (suc (square t)))) := by
  obtain ⟨h⟩ := h
  obtain ⟨d⟩ := actualDiscreteOrderBoundary body α s t
  rw [onEquality] at d
  have hd := Derivation.implicationElimination (weakenClosed d Gamma) h
  have hl : Nonempty (Derivation body (ltF (suc s) t :: Gamma)
      (ltF (square (suc s)) (suc (square t)))) :=
    rightSuccessor _ _ (squareStrictMonotonicity (suc s) t ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hl⟩ := hl
  have he : Derivation body (eqn (suc s) t :: Gamma)
      (ltF (square (suc s)) (suc (square t))) :=
    equalToNext (squareCongr (Derivation.hypothesis List.mem_cons_self))
  exact ⟨disjunctionElimination hd (Derivation.implicationIntroduction hl)
    (Derivation.implicationIntroduction he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSquareRootArithmeticSupportProof
