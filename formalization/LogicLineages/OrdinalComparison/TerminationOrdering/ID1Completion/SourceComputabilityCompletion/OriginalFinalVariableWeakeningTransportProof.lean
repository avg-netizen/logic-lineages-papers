module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningLeafProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformDescentSelection (Data)
open InternalRecursionClosureLogicProof (closedApply)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalVariableLeaves OriginalFinalVariableWeakening
open OriginalFinalVariableWeakeningSupportProof OriginalFinalVariableWeakeningLeafProof
open OriginalTransparentLambdaFinalLogicProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Each normalized original leaf keeps its entire output at the actual
successor index/cons context. The added head is entirely unrestricted. -/
theorem leafTransport (guard : Program 1) (data : Data)
    (out raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma
      (Shape raw shifted variableCode shiftedVariable typ index parameter extendedParameter
        context gamma extendedGamma addedType))) :
    let N := OriginalHereditaryValidity.normalizedData (refineData guard data)
    Nonempty (Derivation body Gamma
      ((graph2 N.oldSource out raw parameter).iff
        (graph2 N.oldSource out shifted extendedParameter))) ∧
    Nonempty (Derivation body Gamma
      ((graph2 N.oldTarget out raw parameter).iff
        (graph2 N.oldTarget out shifted extendedParameter))) := by
  have hv := andLeft hs
  have hvs := andLeft (andRight hs)
  have hr := andLeft (andRight (andRight hs))
  have hrs := andLeft (andRight (andRight (andRight hs)))
  have hp := andLeft (andRight (andRight (andRight (andRight hs))))
  have hg := andLeft (andRight (andRight (andRight (andRight (andRight hs)))))
  have hps := andRight (andRight (andRight (andRight (andRight (andRight hs)))))
  have hd := iffReverse (closedApply
    (OriginalVariableDecoderInternalProof.actualOriginalVariableDecoderConsSuccessor
      body alpha (numeral 1) typ index extendedGamma addedType gamma) hg)
  have hsource := iffCompose
    (sourceLeafEquation guard data out raw variableCode typ index parameter context gamma hv hr hp)
    (iffCompose (booleanIff out (andIff (iffSelf _) hd))
      (iffReverse (sourceLeafEquation guard data out shifted shiftedVariable typ
        (OrdinaryArithmetic.succTerm index) extendedParameter context extendedGamma hvs hrs hps)))
  have htarget := iffCompose
    (targetLeafEquation guard data out raw variableCode typ index parameter context gamma hv hr hp)
    (iffCompose (booleanIff out (andIff (iffSelf _) hd))
      (iffReverse (targetLeafEquation guard data out shifted shiftedVariable typ
        (OrdinaryArithmetic.succTerm index) extendedParameter context extendedGamma hvs hrs hps)))
  exact ⟨hsource,htarget⟩

/-- Both literal OTHER tests follow from the same two variable constructors
already required by the frozen antecedent. -/
theorem otherBoth
    (raw shifted variableCode shiftedVariable typ index parameter extendedParameter
      context gamma extendedGamma addedType : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma
      (Shape raw shifted variableCode shiftedVariable typ index parameter extendedParameter
        context gamma extendedGamma addedType))) :
    Nonempty (Derivation body Gamma
      (graph1 OriginalLambdaTraversalInternal.otherTag (numeral 1) raw)) ∧
    Nonempty (Derivation body Gamma
      (graph1 OriginalLambdaTraversalInternal.otherTag (numeral 1) shifted)) :=
  ⟨variableOther raw (packedVariableTag raw variableCode typ index
      (andLeft hs) (andLeft (andRight (andRight hs)))),
    variableOther shifted (packedVariableTag shifted shiftedVariable typ
      (OrdinaryArithmetic.succTerm index) (andLeft (andRight hs))
      (andLeft (andRight (andRight (andRight hs)))))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningTransportProof
