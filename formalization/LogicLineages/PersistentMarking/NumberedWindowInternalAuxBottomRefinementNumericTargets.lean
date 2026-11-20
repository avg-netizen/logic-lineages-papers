module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowInternalAuxBottomRefinement
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowAtomicPositiveTargets (packedAddress bottomAddress)
open NumberedWindowAtomicApplicationTargets (auxRaw)
open NumberedWindowAtomicApplicationReductionTargets (AuxAcceptedHop)
open NumberedWindowAtomicRawStep (bottomRaw)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings scalar admitted least)
open NumberedWindowConcreteCheckers (positive)
open NumberedWindowAddressAlgorithm (contextView)
open NumberedWindowFieldAlgorithm (unpack)

def packedAuxBottom (c domain codomain stored arg : Nat) : Nat :=
  packedAddress c codomain (auxRaw domain codomain (bottomRaw stored) arg)

/-- Actual all-raw total recognition, with the outer result exactly
the raw codomain and no imposed condition on the other coordinates. -/
def ExactNumericAuxBottomRecognizer : Prop :=
  ∀ x,
    (run sourceFlag x = 1 ↔ ∃ c domain codomain stored arg, x = packedAuxBottom c domain codomain stored arg) ∧
    (run sourceFlag x = 0 ∨ run sourceFlag x = 1)

/-- Terminal shape of the same accepted original supplied witness.
The one actual hop has exact original raw admitted whole bottom and
its own least equality. These also pay the actual scalar(y), not an
extra premise, even for arbitrary Settings. -/
def ExactConcreteAuxBottomAddressPositive : Prop :=
  ∀ (xs : Entries) (s : Settings) c domain codomain stored arg witness y,
    positive xs s (packedAuxBottom c domain codomain stored arg) witness y = true →
    ∃ Γ hop,
      contextView c = some Γ ∧ unpack witness = some [hop] ∧
      AuxAcceptedHop xs s Γ codomain domain codomain (bottomRaw stored) arg hop (bottomRaw codomain) ∧
      y = bottomAddress c codomain ∧ admitted s Γ codomain (bottomRaw codomain) = true ∧
      least s Γ codomain (bottomRaw codomain) = some (bottomRaw codomain) ∧ scalar s y = true

/-- No source-positive preservation assumption beyond actual old
all-raw calibration. In particular the added scalar guard on this one
shape is proved from the actual positive checker. -/
def ExactOriginalAuxBottomRefinement : Prop :=
  ∀ (xs : Entries) (s : Settings) (i : Program 1) (r : Program 3),
    (∀ y, run i y = (scalar s y).toNat) →
    (∀ x w y, evaluate r (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat) →
    ∀ x w y, evaluate (refineAuxBottom i r) (x ::ᵥ w ::ᵥ y ::ᵥ nil) = (positive xs s x w y).toNat

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxBottomRefinementNumericTargets
