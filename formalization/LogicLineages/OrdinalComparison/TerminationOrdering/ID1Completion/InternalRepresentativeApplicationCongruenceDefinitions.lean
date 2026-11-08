module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeFoldCalibrationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruence
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The exact tag wrapper around the exact folded representative Data. The
validity is recursiveData, the source and target wrappers stay distinct, and
the old step Program is preserved. No internal congruence is a data field. -/
def data (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) : InternalQuotientEdgeChecker.Data :=
  InternalRepresentativeTag.withRepresentatives
    (InternalApplicationValidityStack.recursiveData validity member)
    (InternalRepresentativeFoldCalibration.foldedData validity member old)

/-- Actual success graph supplier for the unchanged representative normalizer,
with its own fixed 2*original-payload+1 fuel. External all-input calibration
does not turn this concrete Program into an internally proved constant. -/
def goodRun (validity : InternalOriginalStepGuard.Data) (member : Program 1)
    (old : InternalQuotientEdgeChecker.Data) : Program 1 :=
  InternalApplicationCertifiedResultFoldClosure.goodRun
    (InternalRepresentativeFoldCalibration.rootGuard validity member)
    (InternalRepresentativeFoldCalibration.leaf validity member old)
    (InternalRepresentativeFoldCalibration.combine old)

/-- Common LOCAL opened-root premises. Original typed child/pair/application
graphs are retained literally. The function and parent are source-valid;
both child runs are certified and the argument is fixed by the actual N AST.
The proposed output is the actual combine result on [d,e,x,arg]. The separate
target statement supplies the chosen source or target representative graph
at x. No equality of x with N(fn), normalizer type invariant, output bound,
calibration, or representative-congruence premise is inserted. -/
def applicationPremises {α : Type} (validity : InternalOriginalStepGuard.Data)
    (member : Program 1) (old : InternalQuotientEdgeChecker.Data)
    (arrow d e fp ap fn arg parent x out : OTerm α) : Formula α :=
  InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
    (graph1 (InternalApplicationValidityStack.recursiveData validity member).sourceValid
        InternalOriginalStepGuard.one fn ⊓
      (graph1 (goodRun validity member old) InternalOriginalStepGuard.one fn ⊓
        (graph1 (goodRun validity member old) InternalOriginalStepGuard.one arg ⊓
          (graph1 (InternalRepresentativeFoldCalibration.normalizer validity member old) arg arg ⊓
            (graph1 (InternalApplicationValidityStack.recursiveData validity member).sourceValid
                InternalOriginalStepGuard.one parent ⊓
              graph4 (InternalRepresentativeFoldCalibration.combine old) out d e x arg)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRepresentativeApplicationCongruence
