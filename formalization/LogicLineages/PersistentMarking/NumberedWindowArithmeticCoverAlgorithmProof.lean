import LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmProof
open NumberedWindowArithmeticCoverAlgorithmTargets NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticHeadCode NumberedWindowArithmeticTyCode NumberedWindowSyntax
open NumberedWindowArithmeticFields NumberedWindowFieldAlgorithm
open NumberedWindowPrimaryCoverSyntax

theorem paired : ExactPairedGrammar := by
  intro H K maxN depth
  induction depth with
  | zero => rfl
  | succ n ih =>
    simp only [NumberedWindowCoverAlgorithm.grammar,grammar,ih]
    cases h : grammar H K maxN n with
    | mk ts as =>
      simp [NumberedWindowCoverAlgorithm.leaves,NumberedWindowCoverAlgorithm.namedLeaves,
        NumberedWindowCoverAlgorithm.lambdas,NumberedWindowCoverAlgorithm.ordinary,
        NumberedWindowCoverAlgorithm.numbered,NumberedWindowCoverAlgorithm.applications,
        NumberedWindowCoverAlgorithm.cells,leaves,lambdas,ordinaryHeads,numberedHeads,
        auxiliaryApps,argumentCells,List.flatMap_map,List.map_flatMap,List.map_map,
        Function.comp_def,encodeTerm,encodeArgs,
        NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.1,
        NumberedWindowActualPairAlgorithmChecks.currentPair]

theorem actual : ExactOriginalCover := by
  intro S K q
  exact congrArg Prod.fst (paired (NumberedWindowHeadEnumerationTargets.admittedHeads S K) K
    (termBounds q).numeral (termBounds q).nodes)
end LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverAlgorithmProof
