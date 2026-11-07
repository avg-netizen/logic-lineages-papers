module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationGuardedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalComputabilityApplication InternalComputabilityApplicationProof
open InternalRecursionClosureLogicProof GuardedSourceCertificateProof ApplicationGuardedActivationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only the fixed context and type-code arithmetic are evaluated externally.
Their internal proofs are built by the already proved original numeral evaluator. -/
theorem closedMetadata {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (window : Program 1) (arrow : Program 2) (context : Nat) (sigma tau : Ty)
    (hw : evaluate window (List.Vector.ofFn ![context]) = 1)
    (ha : evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) =
      typeNumber (.arrow sigma tau)) :
    Nonempty (Derivation body Gamma (metadata window arrow (numeral context) sigma tau)) := by
  obtain ⟨dw⟩ := windowNumeral (body := body) (Gamma := Gamma) window context hw
  obtain ⟨da⟩ := arrowNumeral (body := body) (Gamma := Gamma) arrow sigma tau ha
  exact ⟨Derivation.conjunctionIntroduction dw da⟩

/-- Extend the existing source package using its actual construction. The
selected pair is shared by all original closure rules and all new application
rules; no clauses are borrowed from a different existential presentation. -/
theorem actualUniformSourceComputableApplication :
    InternalComputabilityApplicationSourceTargets.ActualUniformSourceComputableApplication := by
  intro n arity
  obtain ⟨src,old,hs,hc,hclosure,hguard⟩ :=
    GammaGuardedSourceProof.actualUniformGuardClosureExists n arity
  obtain ⟨window,hw⟩ := GuardCalibrationProof.actualValidWindowProgram n
  obtain ⟨arrow,ha⟩ := Proof.allPrimitiveFunctions 2 ApplicationDomain.arrowValue
    ApplicationDomainProgramProof.arrowPrimitive
  obtain ⟨result,success,hr,_,_⟩ := ApplicationResultBuilderProof.actualProgramWitnesses n arity
  let comp := InternalApplication.computability old window arrow result
  have hcomp := InternalApplicationCalibrationProof.actualCalibration
    n arity old window arrow result hc hw ha hr
  refine ⟨src,comp,result,hs,hcomp,hr,?_,?_⟩
  · intro symbols S table hclosed α
    let context := OrdinaryArithmeticQuotient.contextCode symbols S table
    have hwindow : evaluate window (List.Vector.ofFn ![context]) = 1 := by
      rw [hw]
      exact (GuardCalibrationProof.actualOriginalWindowCalibration n symbols S table).mpr hclosed
    have harrow (sigma tau : Ty) :
        evaluate arrow (List.Vector.ofFn ![typeNumber sigma,typeNumber tau]) =
          typeNumber (.arrow sigma tau) := by
      rw [ha]
      rfl
    obtain ⟨htyped,hground⟩ := hclosure symbols S table hclosed α
    refine ⟨htyped,hground,?_,?_,?_,?_⟩
    · intro sigma tau f a
      exact ApplicationGuardedApplicationProof.actualOriginalTotality
        (SourcePresentation.sourceBody src context) old window arrow result
        context sigma tau hwindow (harrow sigma tau) α f a
    · intro sigma tau f a out other
      exact ApplicationGuardedApplicationProof.actualOriginalFunctionality
        (SourcePresentation.sourceBody src context) old window arrow result
        context sigma tau hwindow (harrow sigma tau) α f a out other
    · intro sigma tau f a out
      exact closedApply (actualOriginalApplicationComputability
        (SourcePresentation.sourceBody src context) old window arrow result α
        sigma tau (numeral context) f a out)
        (closedMetadata window arrow context sigma tau hwindow (harrow sigma tau))
    · intro sigma tau f a out
      exact closedApply (actualOriginalResultComputability
        (SourcePresentation.sourceBody src context) old window arrow result α
        sigma tau (numeral context) f a out)
        (closedMetadata window arrow context sigma tau hwindow (harrow sigma tau))
  · exact hguard

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityApplicationSourceProof
