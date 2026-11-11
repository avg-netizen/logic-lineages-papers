module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseDecoderInternalFuelNumericSyntaxProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem repeatZeroValue (transition : Program 2) (initial c : OTerm alpha) :
    Nonempty (Derivation body Gamma (repeatGraph transition initial z initial c)) :=
  recursionZeroValue (.projection 0) (repeatStep transition) initial ![initial,c]
    (projectionValue 0 ![initial,c])

theorem repeatZeroRecover (transition : Program 2) (out initial c : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (repeatGraph transition out z initial c))) :
    Nonempty (Derivation body Gamma (eqn out initial)) :=
  valueUnique (repeatProgram transition) out initial ![z,initial,c]
    h (repeatZeroValue transition initial c)

theorem repeatStepValue (transition : Program 2) (count result initial out c : OTerm alpha)
    (h : Nonempty (Derivation body Gamma (graph2 transition out result c))) :
    Nonempty (Derivation body Gamma (programGraph (repeatStep transition) out ![count,result,initial,c])) := by
  apply compositionValue transition ![.projection 1,.projection 3] out
    ![count,result,initial,c] ![result,c] h
  intro i
  exact Fin.cases (projectionValue 1 ![count,result,initial,c])
    (Fin.cases (projectionValue 3 ![count,result,initial,c]) (fun k => Fin.elim0 k)) i

theorem repeatSuccValue (transition : Program 2) (count result out initial c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result count initial c)))
    (ht : Nonempty (Derivation body Gamma (graph2 transition out result c))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) initial c)) :=
  InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction
    Gamma (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 2)))
    (OrdinaryArithmetic.graphFormula (repeatStep transition)) out count result
    ![initial,c] hr (repeatStepValue transition count result initial out c ht)

theorem repeatSuccRecover (transition : Program 2) (count result out initial c : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result count initial c)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) initial c))) :
    Nonempty (Derivation body Gamma (graph2 transition out result c)) := by
  apply programCases transition (Fin.cons result (Fin.cons c Fin.elim0)) _
  intro beta j Delta value hj hv
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hv
  have hr' := renameInto hr j Delta hj
  rw [repeatRename] at hr'
  have ho' := renameInto ho j Delta hj
  simp only [repeatRename,sucRelabel] at ho'
  have hvalue := repeatSuccValue transition (count.relabel j)
    (result.relabel j) value (initial.relabel j) (c.relabel j) hr' hv
  have he := valueUnique (repeatProgram transition) value (out.relabel j)
    ![suc (count.relabel j),initial.relabel j,c.relabel j] hvalue ho'
  exact outputTransport transition value (out.relabel j) ![result.relabel j,c.relabel j] he hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSupportProof
