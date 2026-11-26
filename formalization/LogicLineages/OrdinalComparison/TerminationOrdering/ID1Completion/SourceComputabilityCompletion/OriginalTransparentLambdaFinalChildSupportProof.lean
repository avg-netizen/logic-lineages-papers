module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionEqualityProof
open InternalSourceInversionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalTransparentLambdaFinal
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalExtensionProof
open OriginalTransparentLambdaFinalChildSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Existential root witnesses cannot choose a different body or parameter:
original initial/selector functionality identifies them at the requested
same initial state and transports the identical validator graph. -/
theorem finalChildAt (valid : Program 2)
    (raw parameter state child childParameterCode : OTerm alpha)
    (hi : Nonempty (Derivation body Gamma (graph2 initial state raw parameter)))
    (hc : Nonempty (Derivation body Gamma (graph1 currentBody child state)))
    (hp : Nonempty (Derivation body Gamma (graph1 childParameter childParameterCode state)))
    (hl : Nonempty (Derivation body Gamma (FinalLambdaChild valid raw parameter))) :
    Nonempty (Derivation body Gamma (graph2 valid (numeral 1) child childParameterCode)) := by
  apply finalChildCases valid raw parameter _ hl
  intro beta j Delta actualState actualChild actualParameter hj fields
  simp only [graph2Rename,oneRename]
  have hi' := renameInto hi j Delta hj
  rw [graph2Rename] at hi'
  have hc' := renameInto hc j Delta hj
  rw [graph1Rename] at hc'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  have heState := valueUnique initial actualState (state.relabel j)
    (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) (andLeft fields) hi'
  have hactualChild := headTransport currentBody actualChild actualState (state.relabel j)
    Fin.elim0 heState (andLeft (andLeft (andRight fields)))
  have hactualParameter := headTransport childParameter actualParameter actualState (state.relabel j)
    Fin.elim0 heState (andLeft (andRight (andRight fields)))
  have heChild := valueUnique currentBody actualChild (child.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) hactualChild hc'
  have heParameter := valueUnique childParameter actualParameter (childParameterCode.relabel j)
    (Fin.cons (state.relabel j) Fin.elim0) hactualParameter hp'
  apply graphInputTransport body beta 2 Delta (OrdinaryArithmetic.graphFormula valid)
    (numeral 1) (Fin.cons actualChild (Fin.cons actualParameter Fin.elim0))
    (Fin.cons (child.relabel j) (Fin.cons (childParameterCode.relabel j) Fin.elim0)) _
    (andRight (andRight (andRight fields)))
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)) i
  · rw [onEquality]; exact heChild
  · rw [onEquality]; exact heParameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalChildSupportProof
