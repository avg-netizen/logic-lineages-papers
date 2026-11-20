module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowConcreteFormulaTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericTargets
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowInternalPositiveEndpointRefinement
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowFormulaCalibrationTargets (Evaluates)

/-- The literal normalized conjunction, for arbitrary scalar and
positive ASTs, all three raw numbers, and even non-bit old values. -/
def ExactNumericEndpointCarrierBranches : Prop :=
  ∀ (i : Program 1) (r : Program 3) (x w y : Nat),
    evaluate (withEndpointCarriers i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
      if evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = 1 ∧ run i x = 1 ∧ run i y = 1 then 1 else 0

/-- The actual original positive Boolean is unchanged on all raw
codes after the two physical carrier tests. No original-positive
carrier or typed-domain premise is given to the theorem. -/
def ExactOriginalPositiveEndpointRefinement : Prop :=
  ∀ (entries : Entries) (s : Settings) (i : Program 1) (r : Program 3),
    (∀ x, run i x = (scalar s x).toNat) →
    (∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive entries s x w y).toNat) →
    ∀ x w y,
      evaluate (withEndpointCarriers i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) =
        (positive entries s x w y).toNat

/-- Only the actual positive AST changes in this numerical evaluation
contract; the other three chosen programs remain literal. -/
def ExactOriginalPositiveEndpointPresentationEvaluation : Prop :=
  ∀ (entries : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks entries s) i j r d →
    Evaluates (checks entries s) i j (withEndpointCarriers i r) d

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementNumericTargets
