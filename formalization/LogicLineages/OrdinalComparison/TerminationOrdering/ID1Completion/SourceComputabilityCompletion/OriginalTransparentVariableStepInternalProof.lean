module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorLeafInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight sameAccept)
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalTransparentVariableStep OriginalTransparentVariableStepTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- A concrete original root certificate is accepted without asking the
opaque oldStep for a new value at the transformed code. -/
theorem introduction (source : Program 2) (oldStep : Program 4)
    (s t cert typ parameter : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 source (suc z) s parameter)))
    (hv : Nonempty (Derivation body Delta (graph1 OriginalConstructorLeaf.variableTest (suc z) s)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ)))
    (hc : Nonempty (Derivation body Delta (graph1 certificateCode cert s))) :
    Nonempty (Derivation body Delta (graph4 (refined source oldStep) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hvAt := unaryValue OriginalConstructorLeaf.variableTest (.projection 0) (suc z) s xs hv
    (projectionValue 0 xs)
  have hcAt := unaryValue certificateCode (.projection 0) cert s xs hc (projectionValue 0 xs)
  have hsameCert := sameAccept (.projection 2)
    (.composition certificateCode (fun _ : Fin 1 => .projection 0)) cert xs
    (projectionValue 2 xs) hcAt
  have ha := conjunctionAccept OriginalConstructorLeaf.variableAt
    (InternalApplicationStepPeel.same (.projection 2)
      (.composition certificateCode (fun _ : Fin 1 => .projection 0))) xs hvAt hsameCert
  have htypeAt := unaryValue InternalUnpair.left (.projection 0) typ s xs ht (projectionValue 0 xs)
  have hbAt := unaryValue BottomRepresentative.bottomCode (leftOf (.projection 0)) t typ xs hb htypeAt
  have hsameBottom := sameAccept (.projection 1) OriginalConstructorLeaf.expectedBottom t xs
    (projectionValue 1 xs) hbAt
  have hsAt := binaryValue source (.projection 0) (.projection 3) (suc z) s parameter xs hs
    (projectionValue 0 xs) (projectionValue 3 xs)
  have hout := conjunctionAccept (sourceAt source)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom)
    xs hsAt hsameBottom
  exact successorBranchIntro active oldStep (acceptedValue source) (suc z) z xs ha hout

theorem actualOriginalTransparentVariableStepIntroduction : ActualOriginalTransparentVariableStepIntroduction := by
  intro source oldStep body alpha Delta s t cert typ parameter
  let A := graph2 source InternalOriginalStepGuard.one s parameter ⊓
    (graph1 OriginalConstructorLeaf.variableTest InternalOriginalStepGuard.one s ⊓
      (graph1 InternalUnpair.left typ s ⊓
        (graph1 BottomRepresentative.bottomCode t typ ⊓ graph1 certificateCode cert s)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := introduction source oldStep s t cert typ parameter (andLeft h)
    (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepInternalProof
