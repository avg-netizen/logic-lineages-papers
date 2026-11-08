module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open InternalRawListRecursion InternalRawListRecursionProof InternalRawListRecursionSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalListCodec InternalListCodecSupportProof SourceComputabilityFormulaSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem repeatZeroValue (transition : Program 2) (initial parameter : OTerm α) :
    Nonempty (Derivation body Gamma (repeatGraph transition initial z initial parameter)) :=
  nilValue (.projection (0 : Fin 2)) (repeatStepP transition) initial
    (Fin.cons initial (Fin.cons parameter Fin.elim0))
    (projectionValue 0 (Fin.cons initial (Fin.cons parameter Fin.elim0)))

theorem repeatZeroRecover (transition : Program 2) (out initial parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (repeatGraph transition out z initial parameter))) :
    Nonempty (Derivation body Gamma (eqn out initial)) :=
  valueUnique (repeatP transition) out initial
    (Fin.cons z (Fin.cons initial (Fin.cons parameter Fin.elim0)))
    h (repeatZeroValue transition initial parameter)

theorem repeatStepValue (transition : Program 2) (head result initial out parameter : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 transition out result parameter))) :
    Nonempty (Derivation body Gamma (programGraph (repeatStepP transition) out
      (Fin.cons head (Fin.cons result (Fin.cons initial (Fin.cons parameter Fin.elim0)))))) := by
  let xs : Fin 4 → OTerm α :=
    Fin.cons head (Fin.cons result (Fin.cons initial (Fin.cons parameter Fin.elim0)))
  apply compositionValue transition ![.projection 1,.projection 3] out xs
    (Fin.cons result (Fin.cons parameter Fin.elim0)) h
  intro i
  exact Fin.cases (projectionValue 1 xs)
    (Fin.cases (projectionValue 3 xs) (fun q => Fin.elim0 q)) i

theorem repeatConsValue (transition : Program 2)
    (code head tail result out initial parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result tail initial parameter)))
    (ht : Nonempty (Derivation body Gamma (graph2 transition out result parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code initial parameter)) :=
  InternalRawListRecursionProof.consValue (.projection (0 : Fin 2)) (repeatStepP transition)
    code head tail result out (Fin.cons initial (Fin.cons parameter Fin.elim0))
    hc hr (repeatStepValue transition head result initial out parameter ht)

theorem repeatConsRecover (transition : Program 2)
    (code head tail result out initial parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result tail initial parameter)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out code initial parameter))) :
    Nonempty (Derivation body Gamma (graph2 transition out result parameter)) := by
  apply programCases transition (Fin.cons result (Fin.cons parameter Fin.elim0)) _
  intro β j Delta value hj hv
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hv
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hr' := renameInto hr j Delta hj
  rw [repeatRename] at hr'
  have ho' := renameInto ho j Delta hj
  rw [repeatRename] at ho'
  have hvalue := repeatConsValue transition (code.relabel j) (head.relabel j) (tail.relabel j)
    (result.relabel j) value (initial.relabel j) (parameter.relabel j) hc' hr' hv
  have he := valueUnique (repeatP transition) value (out.relabel j)
    (Fin.cons (code.relabel j) (Fin.cons (initial.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
    hvalue ho'
  exact outputTransport transition value (out.relabel j)
    (Fin.cons (result.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSupportProof
