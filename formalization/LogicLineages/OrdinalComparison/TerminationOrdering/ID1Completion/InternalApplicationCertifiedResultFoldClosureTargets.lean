module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Exact INTERNAL bridge for the unchanged bounded run and fold. The actual
right-selector and original work/result constructor graphs fix the payload,
singleton visit work and singleton result. Good-run acceptance is conjoined
with the raw fold graph on the left: external calibration cannot erase it.
Initial results are zero and the count is exactly 2*original-payload+1. -/
def ActualOriginalCertifiedResultFoldRunBridge : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (value payload work out singleton : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((graph1 InternalUnpair.right payload value ⊓
      (graph1 visitWork work value ⊓
        graph2 InternalListCodec.consCode singleton out OrdinaryArithmetic.zeroTerm)).imp
      ((certifiedFold guard leaf combine out value).iff
        (InternalApplicationResultStackComposition.actualRun guard leaf combine
          (payloadFuel payload) work OrdinaryArithmetic.zeroTerm singleton))))

/-- Genuine INTERNAL constructor closure with actual success and fold
graphs for both children. The root guard sees the original whole parent.
Original constructor graphs share the domain, codomain and child payloads;
combine sees [domain,codomain,functionOutput,argumentOutput] with no output
bound, type or representative premise. The conclusion retains BOTH the
parent good-run graph and its actual fold output at its own fixed fuel. -/
def ActualOriginalCertifiedResultFoldApplicationClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 1) (combine : Program 4) (α : Type)
    (arrow d e fp ap fn arg parent functionOut argumentOut out : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body []
    ((InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph1 guard InternalOriginalStepGuard.one parent ⊓
        (certifiedFold guard leaf combine functionOut fn ⊓
          (certifiedFold guard leaf combine argumentOut arg ⊓
            graph4 combine out d e functionOut argumentOut)))).imp
      (certifiedFold guard leaf combine out parent)))

/-- EXTERNAL all-input calibration of the concrete additional check. The
already checked generic semantic calibration supplies the exact singleton
final run state on every natural input, even malformed source inputs and
arbitrary guard/leaf/combine outputs. This says nothing about an internal
derivation of goodRun=1 without premises and is not used as reflection. -/
def ActualOriginalResultFoldGoodRunCalibration : Prop :=
  ∀ (guard leaf : Program 1) (combine : Program 4) (value : Nat),
  evaluate (goodRun guard leaf combine) (List.Vector.ofFn ![value]) = 1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertifiedResultFoldClosureTargets
