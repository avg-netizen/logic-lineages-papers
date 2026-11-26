module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTyped
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy)
open NumberedWindowInternalFreshProbeDispatchProgram (Leaves compareNumbers bothOne dispatch)
open NumberedWindowInternalFreshProbeEmitter (chooseFresh)
open NumberedWindowInternalFreshProbeParsedEmitter (selected rawResult)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowTypedProbe (typed)
open NumberedWindowAddressApplication (application graph)

/-- Keep the requested type at argument zero and take the physical
result field of argument one by the *same* rawResult program. -/
def resultAtSecond : Program 2 :=
  .composition rawResult (Fin.cons (.projection (1 : Fin 2)) Fin.elim0)

def requestedTypeTest : Program 2 :=
  .composition compareNumbers (Fin.cons (.projection (0 : Fin 2))
    (Fin.cons resultAtSecond Fin.elim0))

/-- Put the real guarded annotation test into the base-typed leaf.
This changes the chosen AST; it does not replace an old proof by
external numerical function equality. -/
def baseWithResult (priorTyped : Program 2) : Program 2 :=
  bothOne priorTyped requestedTypeTest

structure Inputs where
  priorTyped : Program 2
  optionApplication : Program 2
  applicationGuard : Program 3
  scalarProg : Program 1
  freshBound : Program 1

def chosenA (i : Inputs) : Program 1 :=
  chooseFresh (selected i.scalarProg i.freshBound)

def chosenLeaves (i : Inputs) : Leaves :=
  ⟨baseWithResult i.priorTyped, chosenA i, i.optionApplication, i.applicationGuard⟩

def chosenH (i : Inputs) (W : List ProbeTy) : Program 2 :=
  dispatch (chosenLeaves i) W

/-- Original numerical interfaces for the *literal* input leaves, not
any internal typing, arithmetic implication or decoder theorem. -/
def CalibratedInputs (s : Settings) (i : Inputs) : Prop :=
  NumberedWindowInternalFreshProbeParsedEmitter.InputCalibrated s i.scalarProg i.freshBound ∧
  (∀ t q, evaluate i.priorTyped (t ::ᵥ q ::ᵥ nil) = (typed s t q).toNat) ∧
  (∀ q u, evaluate i.optionApplication (q ::ᵥ u ::ᵥ nil) = Encodable.encode (application s q u)) ∧
  (∀ q u v, evaluate i.applicationGuard (q ::ᵥ u ::ᵥ v ::ᵥ nil) = (graph s q u v).toNat)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedTyped
