module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseTuple

/-- A literal arbitrary-open rule on every outer context of this new
body. It does not require or transfer a derivation from an old body. -/
def ExactInstalledPositiveReport : Prop :=
  ∀ (i j cv tv : Program 1) (d : Program 3) (raw : Program 5) (least : Program 3),
    InstalledReportAt i j cv tv d raw least

/-- Select real executable original programs simultaneously. The
working typed dispatch still needs the explicit real ValidWindow. -/
def ExactConcreteInstalledTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j cv tv : Program 1) (d p₀ : Program 3) (raw : Program 5)
      (least : Program 3) (v : Inputs),
      InstalledTupleAt xs s W i j cv tv d p₀ raw least v

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets
