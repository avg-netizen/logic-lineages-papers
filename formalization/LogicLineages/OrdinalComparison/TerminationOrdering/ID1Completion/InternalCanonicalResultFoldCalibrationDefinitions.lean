module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldOpeningDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibration
open Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Specialize the EXACT frozen G at one existing descent selection. The
original root, both original children and original codomain are inspected.
G alone need not agree with V away from applications. -/
def rootGuard (data : InternalCanonicalDescentSelection.Data) : Program 1 :=
  InternalCanonicalResultFoldOpening.rootGuard
    (InternalCanonicalDescentSelection.validity data).sourceValid data.member

/-- D is the same original-fallback descent selector on the WHOLE input. -/
def leaf (data : InternalCanonicalDescentSelection.Data) : Program 1 :=
  InternalCanonicalResultFoldOpening.leaf data.oldEdge.targetRepresentative
    (InternalCanonicalDescentSelection.validity data).sourceValid

/-- D after the ORIGINAL raw application, with inputs
[domain,codomain,functionOutput,argumentOutput]. No codomain repacking. -/
def combine (data : InternalCanonicalDescentSelection.Data) : Program 4 :=
  InternalCanonicalResultFoldOpening.combine data.oldEdge.targetRepresentative
    (InternalCanonicalDescentSelection.validity data).sourceValid

/-- The exact frozen N with unchanged 2*original-payload+1 fuel. -/
def normalizer (data : InternalCanonicalDescentSelection.Data) : Program 1 :=
  InternalCanonicalResultFoldOpening.foldN data.oldEdge.targetRepresentative
    (InternalCanonicalDescentSelection.validity data).sourceValid data.member

/-- The exact frozen H, not an internal success premise or semantic atom. -/
def goodRun (data : InternalCanonicalDescentSelection.Data) : Program 1 :=
  InternalCanonicalResultFoldOpening.goodRunH data.oldEdge.targetRepresentative
    (InternalCanonicalDescentSelection.validity data).sourceValid data.member

/-- Keep the old step literally. Source uses N exactly when V(input)=1 and
is zero otherwise; target uses N on ALL inputs. Selection uses V, not G or
openGuard G, so valid nonapplications retain their original source behavior.
There is no extra tag wrapper, target-universe filter or new Data leaf. -/
def edgeData (data : InternalCanonicalDescentSelection.Data) :
    InternalQuotientEdgeChecker.Data where
  stepProgram := data.oldEdge.stepProgram
  sourceRepresentative := InternalAcceptance.branch
    (InternalApplicationValidityStack.exactOne
      (InternalCanonicalDescentSelection.validity data).sourceValid)
    (InternalAcceptance.constantZero 1) (normalizer data)
  targetRepresentative := normalizer data

/-- The same recursive validity and original canonical typed checker from
the descent selection; only the representative pair changes to N. These are
external all-input calibration propositions, never internal graph rules. -/
def SelectedCalibrated (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (data : InternalCanonicalDescentSelection.Data) : Prop :=
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma
    (InternalCanonicalDescentSelection.validity data) ∧
    (InternalQuotientEdgeChecker.Calibrated n arity symbols S Gamma table
        (edgeData data) ∧
      InternalOriginalTypedCarrier.Calibrated n arity symbols S Gamma
        (InternalCanonicalDescentSelection.selectedTyped data))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalResultFoldCalibration
