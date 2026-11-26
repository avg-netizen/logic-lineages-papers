module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenCallProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeParsedEmitterObjectChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenNodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFixedWindowVertexDispatchSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenShapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (equalEqn)
open ID1Completion.InternalFixedWindowVertexDispatchSupportProof (constantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary rawCons)
open NumberedWindowInternalSparseFieldCell (cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (Reports)
open NumberedWindowInternalSparsePathEnvelopeOpenNodeProof (readNode)
open NumberedWindowInternalFreshProbeParsedEmitter (addressGood addressTag rawContext rawResult rawLeast arrowGood)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets
  (addressTerm addressReports arrowReports sourceShape)
open NumberedWindowInternalFreshProbeParsedEmitterObjectChecks (exact_OpenAddressArrowCoordinates)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem argumentEquation (u c d k : OTerm α)
    (good : Nonempty (Derivation body Γ (unary addressGood (suc z) u)))
    (fields : Nonempty (Derivation body Γ (addressReports u c d k))) :
    Nonempty (Derivation body Γ (eqn u (addressTerm c d k))) := by
  have tag : Nonempty (Derivation body Γ (unary addressTag (numeral 3) u)) := by
    unfold addressTag
    rw [exact_DispatchControlAST.2.1]
    exact constantValue 1 3 ![u]
  obtain ⟨f⟩ := fields
  have r : Reports body Γ u cellTail [c,d,k] :=
    ⟨⟨Derivation.conjunctionLeft f⟩,
      ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight f)⟩,
      ⟨Derivation.conjunctionRight (Derivation.conjunctionRight f)⟩,True.intro⟩
  exact readNode addressTag u (numeral 3) [c,d,k] tag good r

/-- Literal original shells of both inputs, with one shared context
and one common source-domain/argument-result; argument needs no arrow. -/
theorem assembleInputs (f u c r d e l k : OTerm α)
    (leftShape : Nonempty (Derivation body Γ (unary addressGood (suc z) f)))
    (rightShape : Nonempty (Derivation body Γ (unary addressGood (suc z) u)))
    (arrowShape : Nonempty (Derivation body Γ (unary arrowGood (suc z) f)))
    (leftFields : Nonempty (Derivation body Γ (addressReports f c r l)))
    (rightFields : Nonempty (Derivation body Γ (addressReports u c d k)))
    (arrowFields : Nonempty (Derivation body Γ (arrowReports f d e))) :
    Nonempty (Derivation body Γ (parsedApplicationInputs f u c r d e l k)) := by
  have leftLiteral := exact_OpenAddressArrowCoordinates body α Γ f c r d e l
    leftShape arrowShape leftFields arrowFields
  obtain ⟨argLiteral⟩ := argumentEquation u c d k rightShape rightFields
  simp only [sourceShape,equalEqn] at leftLiteral
  obtain ⟨leftEq⟩ := leftLiteral
  obtain ⟨lf⟩ := leftShape
  obtain ⟨rt⟩ := rightShape
  obtain ⟨ar⟩ := arrowShape
  obtain ⟨lv⟩ := leftFields
  obtain ⟨rv⟩ := rightFields
  obtain ⟨av⟩ := arrowFields
  have t0 := Derivation.conjunctionIntroduction (Derivation.conjunctionRight leftEq) argLiteral
  have t1 := Derivation.conjunctionIntroduction (Derivation.conjunctionLeft leftEq) t0
  have t2 := Derivation.conjunctionIntroduction av t1
  have t3 := Derivation.conjunctionIntroduction rv t2
  have t4 := Derivation.conjunctionIntroduction lv t3
  have t5 := Derivation.conjunctionIntroduction ar t4
  have t6 := Derivation.conjunctionIntroduction rt t5
  exact ⟨Derivation.conjunctionIntroduction lf t6⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendOpenShapeProof
