module
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchNumericProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerFitProof
import LogicLineages.PersistentMarking.NumberedWindowInternalBetaSubSelectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalBetaCheckerSelectionProof
public import LogicLineages.PersistentMarking.NumberedWindowConcreteCheckers

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchSelectionProof

open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseRawTickTargets (ActualRoot)
open NumberedWindowInternalBetaRootDispatch (root')
open NumberedWindowInternalBetaSub (betaChecker Fits run2)
open NumberedWindowInternalBetaCheckerFitProof (guardSpec argSpec bodySpec)

/-- The same calibrated selected leaves witness the conservative replacement
for the actual settings-dependent original root dispatcher. -/
theorem selected (entries : NumberedWindowCopyAlgorithm.Entries)
    (s : NumberedWindowScalarAlgorithm.Settings) (original : Program 3)
    (old : ActualRoot (NumberedWindowConcreteCheckers.root entries s) original) :
    ∃ guard arg body sub : Program 2,
      Fits sub ∧
      (∀ src dst, run2 guard src dst = guardSpec src dst) ∧
      (∀ src dst, run2 arg src dst = argSpec src) ∧
      (∀ src dst, run2 body src dst = bodySpec src) ∧
      ActualRoot (NumberedWindowConcreteCheckers.root entries s)
        (root' original (betaChecker guard arg body sub)) := by
  obtain ⟨g,a,b,hg,ha,hb⟩ := NumberedWindowInternalBetaCheckerSelectionProof.selected
  obtain ⟨sub,hs⟩ := NumberedWindowInternalBetaSubSelectionProof.selected
  refine ⟨g,a,b,sub,hs,hg,ha,hb,?_⟩
  apply NumberedWindowInternalBetaRootDispatchNumericProof.exactOriginal
    (NumberedWindowRootDispatchAlgorithm.fixed entries s.window.2) original (betaChecker g a b sub) old
  exact NumberedWindowInternalBetaCheckerFitProof.exactOriginal g a b sub hs hg ha hb

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalBetaRootDispatchSelectionProof
