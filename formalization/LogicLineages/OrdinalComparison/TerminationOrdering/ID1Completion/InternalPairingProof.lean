module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalPairing
open InternalPairingSupportProof InternalArithmeticProgramsSupportProof
open InternalControlGraphSupportProof InternalControlGraphChoiceProof InternalRecursionClosureProof
open InternalTagArithmeticSyntaxProof InternalAdditionLawsProof InternalMultiplicationLawsProof
open InternalOriginalOrderSyntaxProof

theorem actualOriginalPairingGraph : InternalPairingTargets.ActualOriginalPairingGraph := by
  intro body α out x y
  have hy : Nonempty (Derivation body [] ((ltF x y).imp (binaryGraph pairing (add (mul y y) x) x y))) := by
    obtain ⟨d⟩ := pairingOfLess (body := body) (Gamma := [ltF x y]) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  have hn : Nonempty (Derivation body [] ((ltF x y).not.imp
      (binaryGraph pairing (add (add (mul x x) x) y) x y))) := by
    obtain ⟨d⟩ := pairingOfNotLess (body := body) (Gamma := [(ltF x y).not]) x y
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  simpa only [pairingSpec,InternalLessThan.strictLess,equalEqn] using
    (choiceEquation pairing out (add (mul y y) x) (add (add (mul x x) x) y)
      (Fin.cons x (Fin.cons y Fin.elim0)) (ltF x y) hy hn)

theorem actualOriginalPairingTotalFunctional : InternalPairingTargets.ActualOriginalPairingTotalFunctional :=
  fun body => actualOriginalPrograms body 2 pairing

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPairingProof
