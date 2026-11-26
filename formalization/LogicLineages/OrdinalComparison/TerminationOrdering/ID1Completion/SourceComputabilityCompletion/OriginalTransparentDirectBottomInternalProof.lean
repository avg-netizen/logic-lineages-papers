module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTransparentDirectBottom OriginalTransparentDirectBottomTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A concrete original nil-path direct-bottom certificate is accepted from
actual source validity and nonbottom, not an opaque oldStep result. -/
theorem introduction (source : Program 2) (oldStep : Program 4)
    (s t cert typ parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 source (suc z) s parameter)))
    (hn : Nonempty (Derivation body Delta (BottomRepresentative.bottomGraph (suc z) s).not))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hc : Nonempty (Derivation body Delta (graph1 certificateCode cert s))) :
    Nonempty (Derivation body Delta (graph4 (refined source oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hcAt := unaryValue certificateCode (.projection 0) cert s xs hc (projectionValue 0 xs)
  have ha := sameAccept (.projection 2)
    (.composition certificateCode (fun _ : Fin 1 => .projection 0)) cert xs (projectionValue 2 xs) hcAt
  have htypeAt := unaryValue InternalUnpair.left (.projection 0) typ s xs ht (projectionValue 0 xs)
  have hbAt := unaryValue BottomRepresentative.bottomCode (leftOf (.projection 0)) t typ xs hb htypeAt
  have hsameBottom := sameAccept (.projection 1) OriginalConstructorLeaf.expectedBottom t xs (projectionValue 1 xs) hbAt
  have hsAt := binaryValue source (.projection 0) (.projection 3) (suc z) s parameter xs hs
    (projectionValue 0 xs) (projectionValue 3 xs)
  have hnonbottom := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs hn
  have hout := conjunctionAccept (OriginalTransparentVariableStep.sourceAt source) _ xs hsAt
    (conjunctionAccept (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
      (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom) xs hnonbottom hsameBottom)
  exact successorBranchIntro active oldStep (acceptedValue source) (suc z) z xs ha hout

theorem actualOriginalDirectBottomIntroduction : ActualOriginalDirectBottomIntroduction := by
  intro source oldStep body alpha Delta s t cert parameter typ
  let A := Premises source s t cert parameter typ
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := introduction source oldStep s t cert typ parameter (andLeft h)
    (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomInternalProof
