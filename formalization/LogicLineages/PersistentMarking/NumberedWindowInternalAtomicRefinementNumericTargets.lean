module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowAtomicPositiveTargets
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericTargets
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalAtomicRefinement
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowAtomicPositiveTargets (packedAddress freeAddress bottomAddress)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates)

/-- Structural recognizers on ALL original raw numbers, including
malformed contexts/types, sparse gaps, wrong arities and type mismatch.
Outputs are literally 0 or 1, separate from exact recognition. -/
def ExactNumericAtomicRecognizers : Prop :=
  ∀ q : Nat,
    ((run freeSource q = 1 ↔ ∃ c t n, q = freeAddress c t n) ∧
      (run freeSource q = 0 ∨ run freeSource q = 1)) ∧
    ((run bottomSource q = 1 ↔ ∃ c t, q = bottomAddress c t) ∧
      (run bottomSource q = 0 ∨ run bottomSource q = 1))

/-- Literal bottom constructor, physical source fields, and the very
same tape target. No source scalar or type validity premise. -/
def ExactNumericAtomicBottomTarget : Prop :=
  (∀ c t, evaluate bottomEmitter (c ::ᵥ t ::ᵥ nil) = bottomAddress c t) ∧
  (∀ c t k w y,
    evaluate bottomTarget (packedAddress c t k ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if y = bottomAddress c t then 1 else 0)

/-- Standalone exact branch values for arbitrary original Program data.
Outside the two physical atom branches, even a non-bit old value is
retained literally. Normalized success tests exact one only. -/
def ExactNumericRefinedBranches : Prop :=
  ∀ (i : Program 1) (r : Program 3) x w y,
    evaluate (refined i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if run freeSource x = 0 then
        if run bottomSource x = 0 then evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) else 0
      else if evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 ∧
        evaluate bottomTarget (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 ∧ run i y = 1 then 1 else 0

/-- No assumption of source preservation. The only premises are actual
old all-input numerical scalar and original positive calibrations. -/
def ExactOriginalPositiveRefinement : Prop :=
  ∀ (xs : Entries) (s : Settings) (i : Program 1) (r : Program 3),
    (∀ y, run i y = (scalar s y).toNat) →
    (∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) →
    ∀ x w y,
      evaluate (refined i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat

/-- Only the positive checker is replaced in the original full
evaluation contract; original i/j/d physically unchanged. -/
def ExactOriginalRefinedPresentationEvaluation : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d → Evaluates (checks xs s) i j (refined i r) d

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementNumericTargets
