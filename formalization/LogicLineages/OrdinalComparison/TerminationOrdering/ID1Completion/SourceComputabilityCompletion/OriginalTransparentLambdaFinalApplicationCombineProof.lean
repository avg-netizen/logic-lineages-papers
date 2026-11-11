module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationNodeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationValidityFoldInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationCombineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceConjunctionProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalParameterizedApplicationValidityFold
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem combineRecover (node valid : Program 2)
    (d e fo ao fn arg parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 valid fo fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 valid ao arg parameter)))
    (hc : Nonempty (Derivation body Gamma
      (programGraph (combineP node) (numeral 1)
        (Fin.cons d (Fin.cons e (Fin.cons fo (Fin.cons ao (Fin.cons parameter Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma
      (graph2 node (numeral 1) e parameter ⊓
        (graph2 valid (numeral 1) fn parameter ⊓ graph2 valid (numeral 1) arg parameter))) := by
  let xs : Fin 5 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fo (Fin.cons ao (Fin.cons parameter Fin.elim0))))
  have hp := conjunctionRecover (nodeAtP node)
    (InternalAcceptance.conjunction (.projection 2) (.projection 3)) xs hc
  have hchildren := conjunctionRecover (.projection 2) (.projection 3) xs (andRight hp)
  have hn := binaryRecover node (.projection 1) (.projection 4) (numeral 1) e parameter xs
    (andLeft hp) (projectionValue 1 xs) (projectionValue 4 xs)
  have heF := valueUnique (.projection 2) fo (numeral 1) xs
    (projectionValue 2 xs) (andLeft hchildren)
  have heA := valueUnique (.projection 3) ao (numeral 1) xs
    (projectionValue 3 xs) (andRight hchildren)
  exact andIntro hn (andIntro
    (outputTransport valid fo (numeral 1) (Fin.cons fn (Fin.cons parameter Fin.elim0)) heF hf)
    (outputTransport valid ao (numeral 1) (Fin.cons arg (Fin.cons parameter Fin.elim0)) heA ha))

theorem combineValue (node valid : Program 2)
    (d e fo ao fn arg parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 valid fo fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 valid ao arg parameter)))
    (hp : Nonempty (Derivation body Gamma
      (graph2 node (numeral 1) e parameter ⊓
        (graph2 valid (numeral 1) fn parameter ⊓ graph2 valid (numeral 1) arg parameter)))) :
    Nonempty (Derivation body Gamma
      (programGraph (combineP node) (numeral 1)
        (Fin.cons d (Fin.cons e (Fin.cons fo (Fin.cons ao (Fin.cons parameter Fin.elim0))))))) := by
  let xs : Fin 5 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fo (Fin.cons ao (Fin.cons parameter Fin.elim0))))
  have heF := valueUnique valid fo (numeral 1) (Fin.cons fn (Fin.cons parameter Fin.elim0))
    hf (andLeft (andRight hp))
  have heA := valueUnique valid ao (numeral 1) (Fin.cons arg (Fin.cons parameter Fin.elim0))
    ha (andRight (andRight hp))
  have hn := binaryValue node (.projection 1) (.projection 4) (numeral 1) e parameter xs
    (andLeft hp) (projectionValue 1 xs) (projectionValue 4 xs)
  exact conjunctionAccept (nodeAtP node)
    (InternalAcceptance.conjunction (.projection 2) (.projection 3)) xs hn
    (conjunctionAccept (.projection 2) (.projection 3) xs
      (outputTransport (.projection 2) fo (numeral 1) xs heF (projectionValue 2 xs))
      (outputTransport (.projection 3) ao (numeral 1) xs heA (projectionValue 3 xs)))
open OriginalHereditaryValidity
open OriginalHereditaryValidityInternalRecurrenceOutputSupportProof
open OriginalHereditaryValidityInternalRecurrenceOutputBooleanProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open InternalBetaTotalityProof (addHyp)

/-- Transfer every literal combine output once the exact local acceptance
recurrence is established. Rejection is derived from internal Booleanity. -/
theorem combineTransport (node s t m : Program 2)
    (d e fo ao fn arg parent out parameter : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 (validator s t m) fo fn parameter)))
    (ha : Nonempty (Derivation body Gamma (graph2 (validator s t m) ao arg parameter)))
    (he : Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) parent parameter).iff
        (graph2 node (numeral 1) e parameter ⊓
          (graph2 (validator s t m) (numeral 1) fn parameter ⊓
            graph2 (validator s t m) (numeral 1) arg parameter)))))
    (hc : Nonempty (Derivation body Gamma
      (programGraph (combineP node) out
        (Fin.cons d (Fin.cons e (Fin.cons fo (Fin.cons ao (Fin.cons parameter Fin.elim0)))))))) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) out parent parameter)) := by
  let P := graph2 node (numeral 1) e parameter ⊓
    (graph2 (validator s t m) (numeral 1) fn parameter ⊓
      graph2 (validator s t m) (numeral 1) arg parameter)
  let xs : Fin 5 → OTerm alpha :=
    Fin.cons d (Fin.cons e (Fin.cons fo (Fin.cons ao (Fin.cons parameter Fin.elim0))))
  apply formulaCases P
  · have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hcombine := combineValue node (validator s t m) d e fo ao fn arg parameter
      (addAssumption hf P) (addAssumption ha P) hp
    have hout := valueUnique (combineP node) out (numeral 1) xs (addAssumption hc P) hcombine
    obtain ⟨he'⟩ := addAssumption he P
    obtain ⟨hp⟩ := hp
    obtain ⟨hout⟩ := hout
    exact outputTransport (validator s t m) (numeral 1) out
      (Fin.cons parent (Fin.cons parameter Fin.elim0)) ⟨symm hout⟩
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight he') hp⟩
  · let C := programGraph (combineP node) (numeral 1) xs
    have hnC : Nonempty (Derivation body (P.not :: Gamma) C.not) := by
      have hp := combineRecover node (validator s t m) d e fo ao fn arg parameter
        (addAssumption (addAssumption hf P.not) C) (addAssumption (addAssumption ha P.not) C)
        (show Nonempty (Derivation body (C :: P.not :: Gamma) C) from
          ⟨Derivation.hypothesis List.mem_cons_self⟩)
      obtain ⟨hp⟩ := hp
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)) hp)⟩
    have hb := conjunctionOutputBoolean (nodeAtP node)
      (InternalAcceptance.conjunction (.projection 2) (.projection 3)) out xs (addAssumption hc P.not)
    obtain ⟨hz⟩ := booleanOutputReject (combineP node) out xs (addAssumption hc P.not) hb hnC
    let V := graph2 (validator s t m) (numeral 1) parent parameter
    have hnV : Nonempty (Derivation body (P.not :: Gamma) V.not) := by
      obtain ⟨he'⟩ := addAssumption (addAssumption he P.not) V
      exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination
        (Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self))
        (Derivation.implicationElimination (Derivation.conjunctionLeft he')
          (Derivation.hypothesis List.mem_cons_self)))⟩
    exact outputTransport (validator s t m) z out
      (Fin.cons parent (Fin.cons parameter Fin.elim0)) ⟨symm hz⟩
      (validatorReject s t m parent parameter hnV)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationCombineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationCombineProof
