module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCongruenceDivisorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalModularArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDivisibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCongruenceDivisorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalMultiplicationLawsProof InternalAdditionLawsProof
open InternalSourceInversionSupportProof InternalLinearCombinationSyntaxProof
open InternalModularArithmeticProof InternalDivisibilityProof
open InternalDerivationRenamingArithmeticProof InternalDerivationRenamingSyntaxProof

theorem actualDivisor : InternalCongruenceDivisorTargets.ActualDivisor := by
  intro body α Gamma a b d m hd hc
  apply dividesCases Gamma d m _ hd
  intro β j Delta r hi hr
  rw [congruentRename]
  have hc' := renameInto hc j Delta hi
  rw [congruentRename] at hc'
  apply congruenceCases Delta (a.relabel j) (b.relabel j) (m.relabel j) _ hc'
  intro γ f Theta q p hf he
  rw [congruentRename]
  have hr' := renameInto hr f Theta hf
  simp only [eqnRelabel,mulRelabel] at hr'
  obtain ⟨hr'⟩ := hr'
  rw [equationEmbedding] at he
  obtain ⟨he⟩ := he
  let A := (a.relabel j).relabel f
  let B := (b.relabel j).relabel f
  let D := (d.relabel j).relabel f
  let M := (m.relabel j).relabel f
  let R := r.relabel f
  have scale (s : OrdinaryArithmetic.Term γ) :
      Derivation body Theta (eqn (mul (mul s R) D) (mul s M)) :=
    trans (multiplicationAssociativity s R D) (congMulLeft s (symm hr'))
  apply actualIntroduction body γ Theta A B D (mul q R) (mul p R)
  rw [equationEmbedding]
  exact ⟨trans (congAddLeft A (scale q)) (trans he (symm (congAddLeft B (scale p))))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCongruenceDivisorProof
