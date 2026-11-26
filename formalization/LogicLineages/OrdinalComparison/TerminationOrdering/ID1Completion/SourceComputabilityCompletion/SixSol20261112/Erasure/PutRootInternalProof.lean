module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootWorkingTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalConstructorSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof (ordinaryTag)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open PutRoot PutRootWorkingTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

/-- Original pairing inverses recover the SAME label from the original
certificate constructor. No evaluation equality is used internally. -/
theorem certificateLabel (s label cert : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 certificateCode cert s label))) :
    Nonempty (Derivation body Delta (graph1 labelOf label cert)) := by
  exact pathValue (PairPath.right (PairPath.right (PairPath.right (PairPath.here (.projection 1)))))
    (.projection 0) cert label (Fin.cons s (Fin.cons label Fin.elim0))
    (Fin.cons cert Fin.elim0) hc (projectionValue 0 (Fin.cons cert Fin.elim0))
    (projectionValue 1 (Fin.cons s (Fin.cons label Fin.elim0)))

/-- Concrete raw PUT introduction retains every original source/type/head/base,
label, target and certificate at the SAME parameter. -/
theorem introduction (source : Program 2) (oldStep : Program 4)
    (s t cert parameter typ raw head base label : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 source (suc z) s parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta
      (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta (graph2 resultCode t s label)))
    (hc : Nonempty (Derivation body Delta (graph2 certificateCode cert s label))) :
    Nonempty (Derivation body Delta (graph4 (refined source oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hlabel := certificateLabel s label cert hc
  have hlabelAt := unaryValue labelOf (.projection 2) label cert xs hlabel (projectionValue 2 xs)
  have hcertAt := binaryValue certificateCode (.projection 0) labelAt cert s label xs hc
    (projectionValue 0 xs) hlabelAt
  have hactive := sameAccept (.projection 2) certificateAt cert xs (projectionValue 2 xs) hcertAt
  have hraw := unaryValue InternalUnpair.right (.projection 0) raw s xs
    (pairRight s typ raw hp) (projectionValue 0 xs)
  have htag := ordinaryTag (rightOf (.projection 0)) raw head base xs hraw ho
  have hordinary := sameAccept (leftOf (rightOf (.projection 0)))
    (OriginalRawSyntaxTransport.constant 4 4) (numeral 4) xs htag (constantValue 4 xs)
  have hresultAt := binaryValue resultCode (.projection 0) labelAt t s label xs hr
    (projectionValue 0 xs) hlabelAt
  have htarget := sameAccept (.projection 1) resultAt t xs (projectionValue 1 xs) hresultAt
  have hsource := binaryValue source (.projection 0) (.projection 3) (suc z) s parameter xs hs
    (projectionValue 0 xs) (projectionValue 3 xs)
  have hout := conjunctionAccept (OriginalTransparentVariableStep.sourceAt source) _ xs hsource
    (conjunctionAccept ordinaryAt (InternalApplicationStepPeel.same (.projection 1) resultAt)
      xs hordinary htarget)
  exact successorBranchIntro active oldStep (acceptedValue source) (suc z) z xs hactive hout

theorem actualOriginalPutIntroduction : ActualOriginalPutIntroduction := by
  intro source oldStep body alpha Delta s t cert parameter typ raw head base label
  let A := Premises source s t cert parameter typ raw head base label
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := introduction source oldStep s t cert parameter typ raw head base label
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootInternalProof
