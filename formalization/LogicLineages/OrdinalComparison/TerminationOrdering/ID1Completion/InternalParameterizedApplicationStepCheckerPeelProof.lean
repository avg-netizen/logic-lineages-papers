module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerPeelWitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerPeelProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationStepChecker
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalParameterizedApplicationStepCheckerSyntaxProof
open InternalParameterizedApplicationStepCheckerPeelWitnessProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualParameterizedOriginalLiftedTransition :
    InternalParameterizedApplicationStepCheckerTargets.ActualParameterizedOriginalLiftedTransition := by
  intro body endpoint α Delta d e arrow s t a certificate k lifted out parameter
  let A := InternalApplicationStepPeel.taggedEdge d e arrow s t a certificate k ⊓
    (endpointGraph endpoint (suc z) d e s t a parameter ⊓
      graph4 edgeLift lifted d e a certificate)
  apply guardedIffAt
  · have h : Nonempty (Derivation body
        (transitionGraph endpoint out lifted parameter :: A :: Delta) A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hv := liftedValue endpoint d e arrow s t a certificate k lifted parameter
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    have hu : Nonempty (Derivation body
        (transitionGraph endpoint out lifted parameter :: A :: Delta) (eqn out certificate)) :=
      valueUnique (transitionP endpoint) out certificate
        (Fin.cons lifted (Fin.cons parameter Fin.elim0))
        ⟨Derivation.hypothesis List.mem_cons_self⟩ hv
    simpa only [equalEqn] using hu
  · have h : Nonempty (Derivation body (equal out certificate :: A :: Delta) A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hv := liftedValue endpoint d e arrow s t a certificate k lifted parameter
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    have he : Derivation body (equal out certificate :: A :: Delta) (eqn out certificate) := by
      simpa only [equalEqn] using (Derivation.hypothesis List.mem_cons_self :
        Derivation body (equal out certificate :: A :: Delta) (equal out certificate))
    exact outputTransport (transitionP endpoint) certificate out
      (Fin.cons lifted (Fin.cons parameter Fin.elim0)) ⟨symm he⟩ hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerPeelProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerPeelProof
