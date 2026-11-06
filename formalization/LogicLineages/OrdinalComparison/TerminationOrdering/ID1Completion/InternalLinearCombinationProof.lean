module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationArithmeticProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalLinearCombination
open InternalLinearCombinationSyntaxProof InternalLinearCombinationArithmeticProof
open InternalTagArithmeticSyntaxProof InternalSourceInversionSupportProof InternalTagArithmeticSupportProof
open InternalAdditionLawsProof InternalMultiplicationLawsProof InternalAdditionCancellationProof
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof InternalBetaDivisionSyntaxProof
open InternalBetaTotalityProof InternalLeastNumberProof InternalLeastNumberSyntaxProof
open SourceComputabilityFormulaSupportProof
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem remainderClosure (a b d q r : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (cf a b d)))
    (ha : Nonempty (Derivation body Gamma (eqn a (add (mul q d) r)))) :
    Nonempty (Derivation body Gamma (cf a b r)) := by
  apply combinationCases Gamma a b d _ h
  intro β j Delta x y z' w hi e
  rw [combinationRename]
  have ha' := renameInto ha j Delta hi
  simp only [eqnRelabel,addRelabel,mulRelabel] at ha'
  obtain ⟨ha'⟩ := ha'
  rw [equationEmbedding] at e
  obtain ⟨e⟩ := e
  apply combinationIntroduction _ _ _ (add (suc z) (mul (q.relabel j) z'))
    (mul (q.relabel j) w) (mul (q.relabel j) x) (mul (q.relabel j) y)
  rw [equationEmbedding]
  exact ⟨linearCombinationRemainderIdentity _ _ _ _ _ _ _ _ _ e ha'⟩

theorem combinationSymmetry (a b d : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (cf a b d))) :
    Nonempty (Derivation body Gamma (cf b a d)) := by
  apply combinationCases Gamma a b d _ h
  intro β j Delta x y z' w _ e
  rw [combinationRename]
  rw [equationEmbedding] at e
  obtain ⟨e⟩ := e
  apply combinationIntroduction _ _ _ y x w z'
  rw [equationEmbedding]
  exact ⟨trans (commutativity _ _) (trans e (congAddLeft _ (commutativity _ _)))⟩

theorem generatorCombination (a b : OrdinaryArithmetic.Term α) :
    Nonempty (Derivation body Gamma (cf a b a)) := by
  apply combinationIntroduction a b a (suc z) z z z
  rw [equationEmbedding]
  have lhs : Derivation body Gamma (eqn (add (mul (suc z) a) (mul z b)) a) :=
    trans (InternalMultiplicationLawsProof.congAddRight _ (multiplicationLeftOne a))
      (trans (congAddLeft a (multiplicationLeftZero b)) (addZero a))
  have rhs : Derivation body Gamma (eqn (add a (add (mul z a) (mul z b))) a) :=
    trans (congAddLeft a (trans (InternalMultiplicationLawsProof.congAddRight _ (multiplicationLeftZero a))
      (trans (leftZero _) (multiplicationLeftZero b)))) (addZero a)
  exact ⟨trans lhs (symm rhs)⟩

theorem actualRemainderClosure : InternalLinearCombinationTargets.ActualRemainderClosure := by
  intro body α a b d q r
  change Nonempty (Derivation body [] ((cf a b d ⊓ arithmeticEmbedding.onFormula (a.equal (add (mul q d) r))).imp (cf a b r)))
  rw [onEquality]
  let p := cf a b d ⊓ eqn a (add (mul q d) r)
  have hp : Derivation body [p] p := Derivation.hypothesis List.mem_cons_self
  obtain ⟨h⟩ := remainderClosure a b d q r
    ⟨Derivation.conjunctionLeft hp⟩ ⟨Derivation.conjunctionRight hp⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualSymmetry : InternalLinearCombinationTargets.ActualSymmetry := by
  intro body α a b d
  obtain ⟨h⟩ := combinationSymmetry (body := body) (Gamma := [cf a b d]) a b d
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualPositiveMinimum : InternalLinearCombinationTargets.ActualPositiveMinimum := by
  intro body α a b
  obtain ⟨hm⟩ := leastNumber (body := body) (arithmeticEmbedding.onFormula (positiveFamily (suc a) b))
  obtain ⟨hg⟩ := generatorCombination (body := body) (Gamma := []) (suc a) b
  have hp : Derivation body [] (existsOne (arithmeticEmbedding.onFormula (positiveFamily (suc a) b))) := by
    apply Derivation.existentialIntroduction (emb a)
    rw [familyInstantiate]
    exact hg
  exact ⟨Derivation.implicationElimination hm hp⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLinearCombinationProof
