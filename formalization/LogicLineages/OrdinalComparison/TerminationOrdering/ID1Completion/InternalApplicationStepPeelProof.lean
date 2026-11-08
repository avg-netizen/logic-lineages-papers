module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelWitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelEvaluationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationStepPeel
open InternalApplicationCertificateConstructorsProof InternalApplicationStepPeelSupportProof
open InternalApplicationStepPeelWitnessProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem actualOriginalTransitionCalibration :
    InternalApplicationStepPeelTargets.ActualOriginalTransitionCalibration :=
  InternalApplicationStepPeelEvaluationProof.actualOriginalTransitionCalibration

theorem actualOriginalLiftedTransition :
    InternalApplicationStepPeelTargets.ActualOriginalLiftedTransition := by
  intro body endpoint α d e arrow s t a certificate k lifted out
  let A := taggedEdge d e arrow s t a certificate k ⊓
    (graph5 endpoint (suc z) d e s t a ⊓ graph4 edgeLift lifted d e a certificate)
  apply guardedIff
  · have h : Nonempty (Derivation body [graph1 (transition endpoint) out lifted,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hv := liftedValue endpoint d e arrow s t a certificate k lifted
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    simpa only [equalEqn] using valueUnique (transition endpoint) out certificate
      (Fin.cons lifted Fin.elim0) ⟨Derivation.hypothesis List.mem_cons_self⟩ hv
  · have h : Nonempty (Derivation body [equal out certificate,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hv := liftedValue endpoint d e arrow s t a certificate k lifted
      (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
    have he : Derivation body [equal out certificate,A] (eqn out certificate) := by
      simpa only [equalEqn] using (Derivation.hypothesis List.mem_cons_self :
        Derivation body [equal out certificate,A] (equal out certificate))
    exact outputTransport (transition endpoint) certificate out (Fin.cons lifted Fin.elim0) ⟨symm he⟩ hv

theorem actualOriginalRejectedTransition :
    InternalApplicationStepPeelTargets.ActualOriginalRejectedTransition := by
  intro body endpoint α state out
  let A := graph1 (guard endpoint) z state
  apply guardedIff
  · have hz : Nonempty (Derivation body [graph1 (transition endpoint) out state,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hv := rejectedValue endpoint state hz
    simpa only [equalEqn] using valueUnique (transition endpoint) out state
      (Fin.cons state Fin.elim0) ⟨Derivation.hypothesis List.mem_cons_self⟩ hv
  · have hz : Nonempty (Derivation body [equal out state,A] A) :=
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    have hv := rejectedValue endpoint state hz
    have he : Derivation body [equal out state,A] (eqn out state) := by
      simpa only [equalEqn] using (Derivation.hypothesis List.mem_cons_self :
        Derivation body [equal out state,A] (equal out state))
    exact outputTransport (transition endpoint) state out (Fin.cons state Fin.elim0) ⟨symm he⟩ hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelProof
