module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalLogicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningLeafProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof
open InternalOriginalUniformContextMembership
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalVariableLeaves OriginalFinalVariableWeakeningSupportProof
open OriginalTransparentLambdaValidityInternal (BooleanOutput)
open OriginalTransparentLambdaFinalLogicProof
open OriginalTransparentLambdaValidityInternalNormalizationSupportProof (normalizationOffBottom)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The actual source membership call loses only its Gamma coordinate,
through the independently proved original arithmetic slice. -/
theorem typeMemberEquation (member : Program 2)
    (out raw variableCode typ parameter context gamma : OTerm alpha)
    (hr : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (typeMember member) out raw parameter).iff
        (graph2 (contextMember member) out typ context))) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hl := unaryValue InternalUnpair.left (.projection 0) typ raw xs
    (pairLeft raw typ variableCode hr) (projectionValue 0 xs)
  have hc := compositionEquation (normalizedMember member) ![leftOf (.projection 0),.projection 1]
    out xs (Fin.cons typ (Fin.cons parameter Fin.elim0))
    (fun i => Fin.cases hl (Fin.cases (projectionValue 1 xs) (fun j => Fin.elim0 j)) i)
  obtain ⟨hs⟩ := InternalOriginalUniformContextMembershipInternalProof.actualOriginalUniformMembershipSlice
    member body alpha Gamma out typ parameter context gamma
  obtain ⟨hp⟩ := hp
  exact iffCompose hc ⟨Derivation.implicationElimination hs hp⟩

/-- Source output is exposed through the actual variable branch and actual
exact-bottom exclusion. This remains valid for every symbolic output. -/
theorem sourceLeafEquation (guard : Program 1) (data : Data)
    (out raw variableCode typ index parameter context gamma : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refineData guard data)).oldSource
          out raw parameter).iff
        (BooleanOutput out
          (graph2 (contextMember data.member) (numeral 1) typ context ⊓
            OriginalVariableDecoder.graph (numeral 1) typ index gamma)))) := by
  have ht := packedVariableTag raw variableCode typ index hv hr
  obtain ⟨hb⟩ := OriginalVariableLeavesInternalProof.actualOriginalVariableLeavesInternalBranches
    guard data body alpha Gamma out raw parameter
  obtain ⟨hc⟩ := variableControl raw parameter ht
  have hbranch := Derivation.conjunctionLeft (Derivation.implicationElimination hb hc)
  exact iffCompose
    (normalizationOffBottom (refineData guard data).oldSource out raw parameter
      (variableNotBottom raw ht))
    (iffCompose ⟨hbranch⟩
      (iffCompose (conjunctionEquation (typeMember data.member) variableCheck
        (Fin.cons raw (Fin.cons parameter Fin.elim0)) out)
        (booleanIff out (andIff
          (typeMemberEquation data.member (numeral 1) raw variableCode typ parameter context gamma hr hp)
          (variableCheckEquation (numeral 1) raw variableCode typ index parameter context gamma hv hr hp)))))

/-- Target retains its actual arbitrary outer-context guard, at unchanged
Context, and its original variable decoder at the selected Gamma/index. -/
theorem targetLeafEquation (guard : Program 1) (data : Data)
    (out raw variableCode typ index parameter context gamma : OTerm alpha)
    (hv : Nonempty (Derivation body Gamma
      (graph1 OriginalRawSyntaxTransport.variableConstructor variableCode index)))
    (hr : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing raw typ variableCode)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalHereditaryValidity.normalizedData (refineData guard data)).oldTarget
          out raw parameter).iff
        (BooleanOutput out
          (graph1 guard (numeral 1) context ⊓
            OriginalVariableDecoder.graph (numeral 1) typ index gamma)))) := by
  have ht := packedVariableTag raw variableCode typ index hv hr
  obtain ⟨hb⟩ := OriginalVariableLeavesInternalProof.actualOriginalVariableLeavesInternalBranches
    guard data body alpha Gamma out raw parameter
  obtain ⟨hc⟩ := variableControl raw parameter ht
  have hbranch := Derivation.conjunctionRight (Derivation.implicationElimination hb hc)
  exact iffCompose
    (normalizationOffBottom (refineData guard data).oldTarget out raw parameter
      (variableNotBottom raw ht))
    (iffCompose ⟨hbranch⟩
      (iffCompose (conjunctionEquation (contextCheck guard) variableCheck
        (Fin.cons raw (Fin.cons parameter Fin.elim0)) out)
        (booleanIff out (andIff
          (contextCheckEquation guard (numeral 1) raw parameter context gamma hp)
          (variableCheckEquation (numeral 1) raw variableCode typ index parameter context gamma hv hr hp)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningLeafProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningLeafProof
