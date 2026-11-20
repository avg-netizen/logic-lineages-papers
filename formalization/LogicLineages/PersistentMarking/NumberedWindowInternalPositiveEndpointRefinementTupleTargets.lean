module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTupleTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowFormulaCalibrationTargets (Evaluates Interprets)
open NumberedWindowPresentationCheckers (checks)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAccessibilityTargets (Rules)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalAtomicRefinementReinstallTargets (TupleAt)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)

/-- Only the physical positive program changes. The unchanged
original checked values supply a fresh interpretation and actual
inference Rules for this very new body, not the prior body. -/
def ExactEndpointRefinedPresentation : Prop :=
  ∀ (xs : Entries) (s : Settings) (i j : Program 1) (r d : Program 3),
    Evaluates (checks xs s) i j r d →
    let R := withEndpointCarriers i r
    let S := data i j R d
    Evaluates (checks xs s) i j R d ∧ Interprets (checks xs s) S ∧ Rules S

/-- The same entire original Inputs record, unchanged W and physical
i/j/d/a/h/p. In particular no p-star replacement takes place. The
tuple's actual typed totality and given-fresh alignment are at the
new presentation, after replacing only the positive Program. -/
def ExactReinstallEndpointRefinedTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∀ (i j : Program 1) (r d : Program 3) (v : Inputs),
      TupleAt xs s W i j r d v →
      TupleAt xs s W i j (withEndpointCarriers i r) d v

/-- One actual original sparse selection supplies both sides. The
old full InstalledTupleAt keeps p = guard i p₀ and its chosen actual
callbacks; the new TupleAt uses that exact same v and i, with the
literal endpoint-refined addressPositive. No naked existential over
a fresh replacement application/checker tuple. -/
def ExactConcreteEndpointRefinedInstalledTuple : Prop :=
  ∀ (xs : Entries) (s : Settings) (W : List ProbeTy), ValidWindow s W →
    ∃ (i j cv tv : Program 1) (d p₀ : Program 3)
      (raw : Program 5) (least : Program 3) (v : Inputs),
      InstalledTupleAt xs s W i j cv tv d p₀ raw least v ∧
        TupleAt xs s W i j (withEndpointCarriers i (addressPositive cv tv raw least)) d v

end LogicLineages.PersistentMarking.NumberedWindowInternalPositiveEndpointRefinementTupleTargets
