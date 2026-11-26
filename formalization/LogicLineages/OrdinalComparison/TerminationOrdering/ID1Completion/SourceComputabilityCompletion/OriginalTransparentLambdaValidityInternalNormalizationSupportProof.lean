module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBottomParameterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (z)
open InternalBetaTotalityProof
open InternalControlGraphChoiceProof (excludedMiddle)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTransparentLambdaValidityInternalBooleanProof
open OriginalTransparentLambdaValidityInternalBottomParameterProof (iffVia)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem nonBottomControl (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw).not)) :
    Nonempty (Derivation body Gamma (graph2 BottomParameter.exactBottom z raw parameter)) := by
  have hz : Nonempty (Derivation body Gamma (graph1 BottomRepresentative.bottomTest z raw)) :=
    sameReject (.projection 0)
      (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => leftOf (.projection 0)))
      (Fin.cons raw Fin.elim0) hn
  exact unaryValue BottomRepresentative.bottomTest (.projection 0) z raw
    (Fin.cons raw (Fin.cons parameter Fin.elim0)) hz
    (projectionValue 0 (Fin.cons raw (Fin.cons parameter Fin.elim0)))

theorem normalizationOffBottom (old : Program 2) (out raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw).not)) :
    Nonempty (Derivation body Gamma
      ((graph2 (BottomParameter.normalized old) out raw parameter).iff (graph2 old out raw parameter))) := by
  let A := graph2 (BottomParameter.normalized old) out raw parameter
  let B := graph2 old out raw parameter
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
  have hz := nonBottomControl raw parameter hn
  obtain ⟨hf⟩ := zeroBranchElim BottomParameter.exactBottom old (BottomParameter.atContext old) out xs
    (addAssumption hz A)
    (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := zeroBranchIntro BottomParameter.exactBottom old (BottomParameter.atContext old) out xs
    (addAssumption hz B)
    (show Nonempty (Derivation body (B :: Gamma) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem normalizationAtBottom (old : Program 2) (out raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hb : Nonempty (Derivation body Gamma (BottomRepresentative.bottomGraph (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (BottomParameter.normalized old) out raw parameter).iff (graph2 old out raw contextOnly))) := by
  obtain ⟨h⟩ := BottomParameterInternalProof.actualParameterizedBottomLeafSlice body old alpha Gamma
    out raw parameter context gammaCode contextOnly
  obtain ⟨hpairs⟩ := andIntro hp hz
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hpairs) hb⟩

theorem normalizationAtCoordinates (old : Program 2) (out raw parameter context gammaCode contextOnly : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing parameter context gammaCode)))
    (hz : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing contextOnly context z)))
    (hslice : Nonempty (Derivation body Gamma
      ((BottomRepresentative.bottomGraph (numeral 1) raw).imp
        ((graph2 old out raw parameter).iff (graph2 old out raw contextOnly))))) :
    Nonempty (Derivation body Gamma
      ((graph2 (BottomParameter.normalized old) out raw parameter).iff (graph2 old out raw parameter))) := by
  let B := BottomRepresentative.bottomGraph (numeral 1) raw
  have hy : Nonempty (Derivation body (B :: Gamma)
      ((graph2 (BottomParameter.normalized old) out raw parameter).iff (graph2 old out raw parameter))) := by
    have hb : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hslice'⟩ := addAssumption hslice B
    exact iffVia _ _ (graph2 old out raw contextOnly)
      (normalizationAtBottom old out raw parameter context gammaCode contextOnly
        (addAssumption hp B) (addAssumption hz B) hb)
      ⟨Derivation.implicationElimination hslice' (Derivation.hypothesis List.mem_cons_self)⟩
  have hn := normalizationOffBottom (body := body) (Gamma := B.not :: Gamma) old out raw parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hy⟩ := hy
  obtain ⟨hn⟩ := hn
  exact ⟨disjunctionElimination (excludedMiddle B)
    (Derivation.implicationIntroduction hy) (Derivation.implicationIntroduction hn)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalNormalizationSupportProof
