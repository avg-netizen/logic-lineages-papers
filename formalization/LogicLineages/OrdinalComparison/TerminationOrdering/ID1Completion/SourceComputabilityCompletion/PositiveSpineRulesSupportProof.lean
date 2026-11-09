module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalAcceptanceNormalizationProof InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalApplicationStepPeelSupportProof (sameAccept)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalOriginalOrderSyntaxProof (ltF)
open UniformCertificateCompletion.PositiveGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem atValue (p : Program 1) (i : Fin 4) (v : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (graph1 p v (xs i)))) :
    Nonempty (Derivation body Gamma (programGraph (markAt p i) v xs)) :=
  unaryValue p (.projection i) v (xs i) xs h (projectionValue i xs)

theorem atRecover (p : Program 1) (i : Fin 4) (v : OTerm α) (xs : Fin 4 → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph (markAt p i) v xs))) :
    Nonempty (Derivation body Gamma (graph1 p v (xs i))) :=
  unaryRecover p (.projection i) v (xs i) xs h (projectionValue i xs)

theorem flagValue (measure : Program 1) (i : Fin 4) (mark : OTerm α)
    (xs : Fin 4 → OTerm α)
    (hm : Nonempty (Derivation body Gamma (graph1 measure mark (xs i))))
    (hf : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left (suc z) mark))) :
    Nonempty (Derivation body Gamma (programGraph (spineTest measure i) (suc z) xs)) := by
  have hflag := unaryValue InternalUnpair.left (markAt measure i) (suc z) mark xs hf
    (atValue measure i mark xs hm)
  exact sameAccept (flagAt measure i) (InternalLessThan.constantOne 4) (suc z) xs
    hflag (InternalLessThanSupportProof.oneConstantValue xs)

theorem flagRecover (measure : Program 1) (i : Fin 4) (mark : OTerm α)
    (xs : Fin 4 → OTerm α)
    (hm : Nonempty (Derivation body Gamma (graph1 measure mark (xs i))))
    (ht : Nonempty (Derivation body Gamma (programGraph (spineTest measure i) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left (suc z) mark)) := by
  have hflag := sameRightRecover (flagAt measure i) (InternalLessThan.constantOne 4)
    (suc z) xs ht (InternalLessThanSupportProof.oneConstantValue xs)
  exact unaryRecover InternalUnpair.left (markAt measure i) (suc z) mark xs hflag
    (atValue measure i mark xs hm)

theorem depthValue (measure : Program 1) (i : Fin 4) (mark depth : OTerm α)
    (xs : Fin 4 → OTerm α)
    (hm : Nonempty (Derivation body Gamma (graph1 measure mark (xs i))))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth mark))) :
    Nonempty (Derivation body Gamma (programGraph (depthAt measure i) depth xs)) :=
  unaryValue InternalUnpair.right (markAt measure i) depth mark xs hd (atValue measure i mark xs hm)

theorem lessValue (measure : Program 1) (sm tm sd td : OTerm α) (xs : Fin 4 → OTerm α)
    (hsm : Nonempty (Derivation body Gamma (graph1 measure sm (xs 0))))
    (htm : Nonempty (Derivation body Gamma (graph1 measure tm (xs 1))))
    (hsd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right sd sm)))
    (htd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm)))
    (hl : Nonempty (Derivation body Gamma (ltF td sd))) :
    Nonempty (Derivation body Gamma (programGraph (depthLess measure) (suc z) xs)) := by
  apply compositionValue InternalLessThan.ltTest
    (Fin.cons (depthAt measure 1) (Fin.cons (depthAt measure 0) Fin.elim0))
    (suc z) xs (Fin.cons td (Fin.cons sd Fin.elim0))
    (InternalLessThanSupportProof.acceptOfLess td sd hl)
  intro i
  exact Fin.cases (depthValue measure 1 tm td xs htm htd)
    (Fin.cases (depthValue measure 0 sm sd xs hsm hsd) (fun k => Fin.elim0 k)) i

theorem lessRecover (measure : Program 1) (sm tm sd td : OTerm α) (xs : Fin 4 → OTerm α)
    (hsm : Nonempty (Derivation body Gamma (graph1 measure sm (xs 0))))
    (htm : Nonempty (Derivation body Gamma (graph1 measure tm (xs 1))))
    (hsd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right sd sm)))
    (htd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm)))
    (hl : Nonempty (Derivation body Gamma (programGraph (depthLess measure) (suc z) xs))) :
    Nonempty (Derivation body Gamma (ltF td sd)) := by
  have h := compositionRecover InternalLessThan.ltTest
    (Fin.cons (depthAt measure 1) (Fin.cons (depthAt measure 0) Fin.elim0))
    (suc z) xs (Fin.cons td (Fin.cons sd Fin.elim0)) hl
    (fun i => Fin.cases (depthValue measure 1 tm td xs htm htd)
      (Fin.cases (depthValue measure 0 sm sd xs hsm hsd) (fun k => Fin.elim0 k)) i)
  exact InternalLessThanProof.lessOfAcceptance td sd h

theorem nonBottomValue (bottom : Program 1) (xs : Fin 4 → OTerm α)
    (hn : Nonempty (Derivation body Gamma (graph1 bottom (suc z) (xs 0)).not)) :
    Nonempty (Derivation body Gamma (programGraph (nonBottomGuard bottom) (suc z) xs)) := by
  let P := programGraph (bottomAt bottom) (suc z) xs
  have hp : Nonempty (Derivation body Gamma P.not) := by
    obtain ⟨ha⟩ := atRecover bottom 0 (suc z) xs
      (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hn'⟩ := withHyp hn P
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn' ha)⟩
  exact zeroBranchIntro (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (bottomAt bottom))
    (InternalLessThan.constantOne 4) (InternalAcceptance.constantZero 4) (suc z) xs
    (normalizeReject (bottomAt bottom) xs hp) (InternalLessThanSupportProof.oneConstantValue xs)

theorem nonBottomRecover (bottom : Program 1) (xs : Fin 4 → OTerm α)
    (hg : Nonempty (Derivation body Gamma (programGraph (nonBottomGuard bottom) (suc z) xs))) :
    Nonempty (Derivation body Gamma (graph1 bottom (suc z) (xs 0)).not) := by
  let P := graph1 bottom (suc z) (xs 0)
  have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hz := successorBranchElim (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (bottomAt bottom))
    (InternalLessThan.constantOne 4) (InternalAcceptance.constantZero 4) (suc z) z xs
    (normalizeAccept (bottomAt bottom) xs (atValue bottom 0 (suc z) xs hp)) (withHyp hg P)
  obtain ⟨he⟩ := valueUnique (InternalAcceptance.constantZero 4) (suc z) z xs hz (constantZeroValue xs)
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply he)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesSupportProof
