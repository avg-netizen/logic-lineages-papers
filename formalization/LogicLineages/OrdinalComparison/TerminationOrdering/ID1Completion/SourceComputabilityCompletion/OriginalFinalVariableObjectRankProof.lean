module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectFixednessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectRankProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open OriginalFinalVariableCanonicalSupportProof (iffForward)
open OriginalFinalVariableObject OriginalFinalVariableObjectInternalSupportProof OriginalFinalVariableObjectFixednessProof
open OriginalRawObjectTransport

/-- Both actual Object endpoints have rank one and preserve every rank
output under the SAME final wrapper. Neither internal rank graph is obtained
from a standard-natural equation. -/
theorem actualOriginalFinalVariableObjectRankPreservation :
    OriginalFinalVariableObjectTargets.ActualOriginalFinalVariableObjectRankPreservation := by
  intro guard p body alpha Delta rank out shiftedOut input shiftedObject raw shifted variableCode shiftedVariable
    typ index parameter extendedParameter context gamma extendedGamma addedType
  let K := canonicalObjectProgram (OriginalVariableLeaves.refineInputs guard p)
  let A := Premise guard p input raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  let B := graph2 shiftObjectRaw shiftedObject addedType input
  let C := graph2 K out context input ⊓ graph2 K shiftedOut context shiftedObject
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hp := andLeft ha
  have hs := andLeft (andRight ha)
  have hcons := andLeft (andRight (andRight (andRight (andRight (andRight hs)))))
  have hrank := objectVariableRankEquation rank input gamma raw variableCode typ index hp
    (andLeft hs) (andLeft (andRight (andRight hs)))
  have ht := OriginalFinalVariableCanonicalRawProof.packedVariableTransport
    raw shifted variableCode shiftedVariable typ index addedType
    (andLeft hs) (andLeft (andRight hs)) (andLeft (andRight (andRight hs)))
    (andLeft (andRight (andRight (andRight hs))))
  have hb : Nonempty (Derivation body (B :: A :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hpair := shiftObjectPair addedType input shiftedObject gamma raw extendedGamma shifted
    (addAssumption hp B) (addAssumption hcons B) (addAssumption ht.1 B) hb
  have hshiftRank := objectVariableRankEquation rank shiftedObject extendedGamma shifted shiftedVariable typ
    (OrdinaryArithmetic.succTerm index) hpair (addAssumption (andLeft (andRight hs)) B)
    (addAssumption (andLeft (andRight (andRight (andRight hs)))) B)
  obtain ⟨hfixed⟩ := actualOriginalFinalVariableObjectFixedness guard p body alpha (A :: Delta)
    out shiftedOut input shiftedObject raw shifted variableCode shiftedVariable typ index
    parameter extendedParameter context gamma extendedGamma addedType
  obtain ⟨ha'⟩ := ha
  have hf := show Nonempty (Derivation body (A :: Delta) _) from
    ⟨Derivation.implicationElimination hfixed ha'⟩
  obtain ⟨hfs⟩ := addAssumption (andRight hf) B
  obtain ⟨hb'⟩ := hb
  have hshiftEquation := show Nonempty (Derivation body (B :: A :: Delta) _) from
    ⟨Derivation.implicationElimination hfs hb'⟩
  have hc : Nonempty (Derivation body (C :: B :: A :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have houtEq := iffForward (addAssumption (addAssumption (andLeft hf) B) C) (andLeft hc)
  have hshiftEq := iffForward (addAssumption hshiftEquation C) (andRight hc)
  obtain ⟨hpreserved⟩ := andIntro
    (unaryInputEquation variableRankObjectRaw rank out input houtEq)
    (unaryInputEquation variableRankObjectRaw rank shiftedOut shiftedObject hshiftEq)
  obtain ⟨hshiftResult⟩ := andIntro hshiftRank
    (show Nonempty (Derivation body (B :: A :: Delta) _) from
      ⟨Derivation.implicationIntroduction hpreserved⟩)
  obtain ⟨hresult⟩ := andIntro hrank
    (show Nonempty (Derivation body (A :: Delta) _) from
      ⟨Derivation.implicationIntroduction hshiftResult⟩)
  exact ⟨Derivation.implicationIntroduction hresult⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectRankProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectRankProof
