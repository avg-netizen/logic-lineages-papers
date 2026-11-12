module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextObserverDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserver
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- [index, previous front, original context]. Original successor/pair list
codes are retained. Out-of-range behavior is total, not a decoding claim. -/
def frontStep : Program 3 :=
  .composition InternalApplicationValidityStackAppend.append
    ![.projection 1, .composition InternalListCodec.consCode
      ![.composition InternalRawListRecursion.lookup ![.projection 0,.projection 2],
        InternalAcceptance.constantZero 3]]
/-- [cutoff,context]. The original forward prefix, never a reversed context. -/
def front : Program 2 := .recursion (InternalAcceptance.constantZero 1) frontStep
/-- [cutoff,context]. Remove precisely the cell at cutoff when it exists. -/
def deleteAt : Program 2 :=
  .composition InternalApplicationValidityStackAppend.append
    ![front,.composition InternalRawListRecursion.drop
      ![.composition .succ (fun _ : Fin 1 => .projection 0),.projection 1]]
/-- [cutoff,packed,parameter]. The selected type is the literal original
context head after cutoff drops; the window code is unchanged. -/
def erasedPacked : Program 3 :=
  .composition OriginalRawSyntaxTransport.erasePackedRaw
    ![.composition InternalRawListRecursion.lookup
      ![.projection 0,rightOf (.projection 2)],.projection 0,.projection 1]
def erasedParameter : Program 3 :=
  pairOf (leftOf (.projection 2))
    (.composition deleteAt ![.projection 0,rightOf (.projection 2)])
/-- A single paired observation, using ONLY the pre-minimum original key. -/
def positionObservation (R : Program 2) : Program 3 :=
  pairOf (.composition R ![erasedPacked,erasedParameter])
    (.composition OriginalRawSyntaxTransport.variableRankPackedRaw
      (fun _ : Fin 1 => erasedPacked))
/-- [cutoff,seed,candidate,parameter]. -/
def positionTest (R : Program 2) : Program 4 :=
  InternalApplicationStepPeel.same
    (.composition (positionObservation R) ![.projection 0,.projection 1,.projection 3])
    (.composition (positionObservation R) ![.projection 0,.projection 2,.projection 3])
/-- [index,previous,seed,candidate,parameter]. -/
def scanStep (R : Program 2) : Program 5 :=
  InternalAcceptance.conjunction (.projection 1)
    (.composition (positionTest R) ![.projection 0,.projection 2,.projection 3,.projection 4])
/-- [bound,seed,candidate,parameter]; empty conjunction is one. -/
def scan (R : Program 2) : Program 4 :=
  .recursion (InternalLessThan.constantOne 3) (scanStep R)
def allTests (R : Program 2) : Program 3 :=
  .composition (scan R)
    ![.composition OriginalContextInsertion.length
      (fun _ : Fin 1 => rightOf (.projection 2)),.projection 0,.projection 1,.projection 2]
/-- No caller-supplied cutoff and no selected tuple occur in this AST.
Inactive and empty-context vectors return the complete original P. For
arbitrary uncalibrated guards, active malformed vectors are total but may be
filtered; the separate calibration target asserts equality on EVERY vector. -/
def classTest (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) (P : Program 3) : Program 3 :=
  InternalAcceptance.branch (rightOf (.projection 2)) P
    (InternalAcceptance.branch
      (.composition (OriginalActiveObservedClass.activation p H G W)
        ![.projection 0,.projection 2]) P
      (InternalAcceptance.conjunction P (allTests p.base.oldRepresentative)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextAllPositionObserver
