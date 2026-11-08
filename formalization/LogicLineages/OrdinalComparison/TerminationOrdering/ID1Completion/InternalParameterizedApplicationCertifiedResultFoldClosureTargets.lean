module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertifiedResultFoldClosure
open InternalParameterizedApplicationCertifiedResultFoldClosure
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- INTERNAL bridge at the original exact succ(payload+payload) fuel.
Actual original selector and singleton constructor graphs fix the payload,
visit work and result singleton. Both whole-state success and raw output
remain on the left. The right retains actual initial and final state witnesses,
empty initial results, and the identical arbitrary symbolic parameter.
No external calibration or semantic truth-to-derivability step is assumed. -/
def ActualOriginalParameterizedCertifiedResultFoldRunBridge : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (value payload work out singleton parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((graph1 InternalUnpair.right payload value ⊓
      (graph1 visitWork work value ⊓
        graph2 InternalListCodec.consCode singleton out OrdinaryArithmetic.zeroTerm)).imp
      ((certifiedFoldP guard leaf combine out value parameter).iff
        (InternalParameterizedApplicationResultStackComposition.actualRunP guard leaf combine
          (payloadFuel payload) work OrdinaryArithmetic.zeroTerm singleton parameter))))

/-- INTERNAL fallback closure in every original body and context. Actual
openGuardP(value,p)=0 and L(value,p)=out imply BOTH actual goodRunP=1 and
actual foldP=out at the original run fuel. Payload, work, singleton results
and states are introduced internally, not supplied as additional premises.
Zero output and malformed original inputs are not excluded. -/
def ActualOriginalParameterizedCertifiedResultFoldLeafClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α)) (value out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((leafGraphsP guard leaf out value parameter).imp
      (certifiedFoldP guard leaf combine out value parameter)))

/-- INTERNAL original application closure. Constructor graphs share the
actual domain, codomain and child payloads. G sees the whole original parent;
both certified children and C use the SAME symbolic p. C receives function
before argument in [d,e,functionOut,argumentOut,p] order. The parent concludes
BOTH actual goodRunP and foldP at its ORIGINAL fuel, with no new padded budget,
source-validity, nonzero-output, type, representative or semantic premise. -/
def ActualOriginalParameterizedCertifiedResultFoldApplicationClosure : Prop :=
  ∀ (body : Positive (Fin 1)) (guard leaf : Program 2) (combine : Program 5) (α : Type)
    (Gamma : List (Formula α))
    (arrow d e fp ap fn arg parent functionOut argumentOut out parameter : OrdinaryArithmetic.Term α),
  Nonempty (Derivation body Gamma
    ((InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg parent ⊓
      (graph2 guard InternalOriginalStepGuard.one parent parameter ⊓
        (certifiedFoldP guard leaf combine functionOut fn parameter ⊓
          (certifiedFoldP guard leaf combine argumentOut arg parameter ⊓
            programGraph combine out
              (Fin.cons d (Fin.cons e (Fin.cons functionOut
                (Fin.cons argumentOut (Fin.cons parameter Fin.elim0))))))))).imp
      (certifiedFoldP guard leaf combine out parent parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationCertifiedResultFoldClosureTargets
