module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationResultFoldCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeTagDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibration
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The exact recursive SOURCE validity AST, applied to the WHOLE original
raw root. The generic fold also tests the original constructor tag at two.
Neither packed-target validity alone nor a child guard can open a root. -/
def rootGuard (validity : InternalOriginalStepGuard.Data) (member : Program 1) : Program 1 :=
  (InternalApplicationValidityStack.recursiveData validity member).sourceValid

/-- Reuse the checked original target-tag wrapper. Its validity leaf has only
packed decoding, with NO universe restriction. Thus malformed and nonuniverse
roots retain the original all-input target representative after calibration. -/
def leaf (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) : Program 1 :=
  InternalRepresentativeTag.representative
    (InternalApplicationValidityStack.recursiveData validity member).targetValid
    old.targetRepresentative

/-- Inputs are exactly [domain,codomain,functionOutput,argumentOutput]. The
original application constructor removes ONLY the two outer child type fields.
The explicit outer pair makes the result tag the supplied codomain, including
on arbitrary off-domain combine inputs. Calibration of the complete fold uses
this combine ONLY at source-universe-valid opened roots, never unconditionally. -/
def combine (old : InternalQuotientEdgeChecker.Data) : Program 4 :=
  pairOf (.projection 1)
    (rightOf (.composition old.targetRepresentative
      (fun _ : Fin 1 => InternalApplicationCertificateConstructors.application)))

/-- The actual existing bounded result-fold AST with its unchanged original
2*payload+1 fuel. No representative law or correctness proof is a data field. -/
def normalizer (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) : Program 1 :=
  InternalApplicationResultStack.fold (rootGuard validity member)
    (leaf validity member old) (combine old)

/-- Source is the common normalizer exactly when the ORIGINAL source guard
returns one, and zero otherwise. Target is the common normalizer on ALL inputs.
The original step program is preserved literally. This concrete Data can be
formed for every window, but its calibration is asserted only for subtype-
closed windows; the fixed-window selection target retains old for other S. -/
def foldedData (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) : InternalQuotientEdgeChecker.Data where
  stepProgram := old.stepProgram
  sourceRepresentative := InternalAcceptance.branch
    (InternalApplicationValidityStack.exactOne (rootGuard validity member))
    (InternalAcceptance.constantZero 1) (normalizer validity member old)
  targetRepresentative := normalizer validity member old

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibration
