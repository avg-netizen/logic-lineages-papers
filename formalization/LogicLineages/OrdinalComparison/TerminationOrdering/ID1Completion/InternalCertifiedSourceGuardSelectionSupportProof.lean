module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalCertifiedSourceGuardSelection
open InternalOriginalTypedCarrierSupportProof (atValue atRecover)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Recover each literal graph; the two run checks are never discharged by
their external calibration. -/
theorem stepRecover (data : Data) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepAccepted data s t k))) :
    Nonempty (Derivation body Gamma (stepFactors data s t k)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  have hb := conjunctionRecover _ _ xs h
  have hv := conjunctionRecover _ _ xs (andRight hb)
  have hr := conjunctionRecover _ _ xs (andRight hv)
  exact andIntro (andLeft hb)
    (andIntro (atRecover (validity data).sourceValid 1 (suc z) xs (andLeft hv))
      (andIntro (atRecover (goodRun data) 0 (suc z) xs (andLeft hr))
        (atRecover (goodRun data) 1 (suc z) xs (andRight hr))))

theorem stepAccept (data : Data) (s t k : OTerm α)
    (h : Nonempty (Derivation body Gamma (stepFactors data s t k))) :
    Nonempty (Derivation body Gamma (stepAccepted data s t k)) := by
  let xs : Fin 3 → OTerm α := Fin.cons s (Fin.cons t (Fin.cons k Fin.elim0))
  exact conjunctionAccept _ _ xs (andLeft h)
    (conjunctionAccept _ _ xs
      (atValue (validity data).sourceValid 1 (suc z) xs (andLeft (andRight h)))
      (conjunctionAccept _ _ xs
        (atValue (goodRun data) 0 (suc z) xs (andLeft (andRight (andRight h))))
        (atValue (goodRun data) 1 (suc z) xs (andRight (andRight (andRight h))))))

/-- Equality-test acceptance recovers the ACTUAL N graph at the known raw
value by the existing internal sameRightRecover theorem. -/
theorem typedRecover (data : Data) (value typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (typedAccepted data value typ))) :
    Nonempty (Derivation body Gamma (typedFactors data value typ)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons typ Fin.elim0)
  have hb := conjunctionRecover _ _ xs h
  have hr := conjunctionRecover _ _ xs (andRight hb)
  have hn := sameRightRecover (unaryAt (normalizer data) 0) (.projection 0)
    value xs (andRight hr) (projectionValue 0 xs)
  exact andIntro (andLeft hb)
    (andIntro (atRecover (goodRun data) 0 (suc z) xs (andLeft hr))
      (atRecover (normalizer data) 0 value xs hn))

theorem typedAccept (data : Data) (value typ : OTerm α)
    (h : Nonempty (Derivation body Gamma (typedFactors data value typ))) :
    Nonempty (Derivation body Gamma (typedAccepted data value typ)) := by
  let xs : Fin 2 → OTerm α := Fin.cons value (Fin.cons typ Fin.elim0)
  have hn := atValue (normalizer data) 0 value xs (andRight (andRight h))
  exact conjunctionAccept _ _ xs (andLeft h)
    (conjunctionAccept _ _ xs
      (atValue (goodRun data) 0 (suc z) xs (andLeft (andRight h)))
      (sameAccept (unaryAt (normalizer data) 0) (.projection 0) value xs hn
        (projectionValue 0 xs)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCertifiedSourceGuardSelectionSupportProof
