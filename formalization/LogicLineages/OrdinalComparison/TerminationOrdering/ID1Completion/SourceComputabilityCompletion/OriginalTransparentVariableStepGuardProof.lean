module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableWeakeningSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalGraphComposition
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof InternalControlGraphProof InternalAcceptanceBranchProof
open InternalAcceptanceConjunctionProof InternalApplicationStepPeelSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Equal branch outputs need no premise on the control, even at malformed
non-Boolean control values. Totality and object-language cases suffice. -/
theorem equalBranches {n : Nat} (control a b : Program n) (out : OTerm alpha)
    (xs : Fin n → OTerm alpha)
    (ha : Nonempty (Derivation body Delta (programGraph a out xs)))
    (hb : Nonempty (Derivation body Delta (programGraph b out xs))) :
    Nonempty (Derivation body Delta
      (programGraph (InternalAcceptance.branch control a b) out xs)) := by
  apply programCases control xs _
  intro beta j Gamma c hj hc
  simp only [programRename]
  have ha' := renameInto ha j Gamma hj
  have hb' := renameInto hb j Gamma hj
  simp only [programRename] at ha' hb'
  have hconditional : Nonempty (Derivation body Gamma
      (programGraph LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
        (out.relabel j) (Fin.cons c (Fin.cons (out.relabel j)
          (Fin.cons (out.relabel j) Fin.elim0))))) := by
    apply formulaCases (eqn c z)
    · exact conditionalAtZero c (out.relabel j) (out.relabel j)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
    · exact conditionalAtNonzero c (out.relabel j) (out.relabel j)
        ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact branchValue control a b (out.relabel j) c (out.relabel j) (out.relabel j)
    (fun i => (xs i).relabel j) hc ha' hb' hconditional

/-- Same-type bottom discharges both implication guards, while literal
variable tag zero discharges actual bottom rejection. -/
theorem guards (endpoint : Program 6) (window : Program 1)
    (s t cert parameter typ : OTerm alpha)
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag z s)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ s)))
    (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) s t cert parameter ⊓
        graph4 (InternalAcceptance.conjunction
          (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
          OriginalConstructorLeaf.variableGuard) (suc z) s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have htype := unaryValue InternalUnpair.left (.projection 0) typ s xs ht (projectionValue 0 xs)
  have hbottom := unaryValue BottomRepresentative.bottomCode (leftOf (.projection 0)) t typ xs hb htype
  have hsame := sameAccept (.projection 1) OriginalConstructorLeaf.expectedBottom t xs
    (projectionValue 1 xs) hbottom
  have hone := InternalLessThanSupportProof.oneConstantValue (body := body) (Gamma := Delta) xs
  have hneutral := equalBranches (OriginalNeutralLeaf.trigger endpoint window)
    (InternalLessThan.constantOne 4)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom)
    (suc z) xs hone hsame
  have hvar := equalBranches
    (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize OriginalConstructorLeaf.variableAt)
    (InternalLessThan.constantOne 4)
    (InternalApplicationStepPeel.same (.projection 1) OriginalConstructorLeaf.expectedBottom)
    (suc z) xs hone hsame
  have hnonbottom := PositiveSpineRulesSupportProof.nonBottomValue BottomRepresentative.bottomTest xs
    (OriginalFinalVariableWeakeningSupportProof.variableNotBottom s htag)
  exact andIntro hneutral (conjunctionAccept _ _ xs hnonbottom hvar)

theorem actualOriginalVariableBottomGuards :
    OriginalTransparentVariableStepGuardTargets.ActualOriginalVariableBottomGuards := by
  intro endpoint window body alpha Delta s t cert parameter typ
  let A := graph1 OriginalLambdaConstructor.tag z s ⊓
    (graph1 InternalUnpair.left typ s ⊓ graph1 BottomRepresentative.bottomCode t typ)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hout⟩ := guards endpoint window s t cert parameter typ (andLeft h)
    (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardProof
