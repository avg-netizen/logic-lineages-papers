module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowAtomicApplicationTargets (AtomHead auxRaw)
open NumberedWindowAtomicPositiveTargets (packedAddress)
open NumberedWindowAddressApplication (graph)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalAtomicRefinement (atSource)
open NumberedWindowInternalFreshProbeParsedEmitter (arrowGood)
open NumberedWindowInternalAtomicApplicationShape

/-- Re-emit exactly the same actual sparse natural-number constructors,
not an encoding of a different syntax or canonical representative. -/
def ExactNumericApplicationEmitters : Prop :=
  (∀ c t k, evaluate addressEmitter (c ::ᵥ t ::ᵥ k ::ᵥ nil) = packedAddress c t k) ∧
  (∀ c d e k a, evaluate auxAddressEmitter (c ::ᵥ d ::ᵥ e ::ᵥ k ::ᵥ a ::ᵥ nil) =
    packedAddress c e (auxRaw d e k a))

/-- These physical additional tests all succeed on each actual original
accepted graph at the specified literal atom-head function address.
No scalar-output or fixed-window precondition. -/
def ExactOriginalAtomTapeCoordinates : Prop :=
  ∀ (s : Settings) c t k u y, AtomHead k →
    graph s (packedAddress c t k) u y = true →
    let tape := packedAddress c t k ::ᵥ u ::ᵥ y ::ᵥ nil
    evaluate (atSource arrowGood) tape = 1 ∧
    evaluate sameArgument tape = 1 ∧ evaluate sameResult tape = 1

/-- Complete original all-raw numerical graph, all Settings. Old graph
calibration is the only premise; new guard preservation is a conclusion. -/
def ExactOriginalShapeRefinedApplication : Prop :=
  ∀ (s : Settings) (p : Program 3),
    (∀ f u y, evaluate p (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (graph s f u y).toNat) →
    ∀ f u y, evaluate (refinedApplication p) (f ::ᵥ u ::ᵥ y ::ᵥ nil) = (graph s f u y).toNat

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeNumericTargets
