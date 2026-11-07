module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalArithmeticPrograms
open InternalArithmeticProgramsSupportProof InternalArithmeticProgramsMultiplicationProof
open InternalControlGraphSupportProof InternalRecursionClosureProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof InternalMultiplicationLawsProof

theorem actualOriginalAdditionGraph : InternalArithmeticProgramsTargets.ActualOriginalAdditionGraph := by
  intro body α out x y
  obtain ⟨hf⟩ := valueUnique (body := body)
    (Gamma := [binaryGraph addition out x y]) addition out (add x y) (Fin.cons x (Fin.cons y Fin.elim0))
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (additionValue x y)
  obtain ⟨hb⟩ := outputTransport (body := body) (Gamma := [eqn out (add x y)])
    addition (add x y) out (Fin.cons x (Fin.cons y Fin.elim0))
    ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (additionValue x y)
  simp only [equalEqn]
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalMultiplicationGraph : InternalArithmeticProgramsTargets.ActualOriginalMultiplicationGraph := by
  intro body α out x y
  obtain ⟨hf⟩ := valueUnique (body := body)
    (Gamma := [binaryGraph multiplication out x y]) multiplication out (mul x y) (Fin.cons x (Fin.cons y Fin.elim0))
    ⟨Derivation.hypothesis List.mem_cons_self⟩ (multiplicationValue x y)
  obtain ⟨hb⟩ := outputTransport (body := body) (Gamma := [eqn out (mul x y)])
    multiplication (mul x y) out (Fin.cons x (Fin.cons y Fin.elim0))
    ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (multiplicationValue x y)
  simp only [equalEqn]
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalAdditionTotalFunctional : InternalArithmeticProgramsTargets.ActualOriginalAdditionTotalFunctional :=
  fun body => actualOriginalPrograms body 2 addition

theorem actualOriginalMultiplicationTotalFunctional : InternalArithmeticProgramsTargets.ActualOriginalMultiplicationTotalFunctional :=
  fun body => actualOriginalPrograms body 2 multiplication

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsProof
