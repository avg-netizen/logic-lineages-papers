module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof InternalAcceptanceNormalizationProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalTagArithmeticSyntaxProof (OTerm z suc)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalBetaTotalityProof (addHyp)
open UniformCertificateCompletion.PositiveGuard
open SourceComputabilityCompletion.PositiveSpineRulesSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem testReject (measure : Program 1) (i : Fin 4) (mark : OTerm α) (xs : Fin 4 → OTerm α)
    (hm : Nonempty (Derivation body Gamma (graph1 measure mark (xs i))))
    (hn : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left (suc z) mark).not)) :
    Nonempty (Derivation body Gamma (programGraph (spineTest measure i) (suc z) xs).not) := by
  let P := programGraph (spineTest measure i) (suc z) xs
  obtain ⟨hf⟩ := flagRecover measure i mark xs (withHyp hm P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hn'⟩ := withHyp hn P
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn' hf)⟩

theorem spineRecover (measure : Program 1) (sm tm sd td : OTerm α) (xs : Fin 4 → OTerm α)
    (hsm : Nonempty (Derivation body Gamma (graph1 measure sm (xs 0))))
    (htm : Nonempty (Derivation body Gamma (graph1 measure tm (xs 1))))
    (hsd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right sd sm)))
    (htd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm)))
    (hg : Nonempty (Derivation body Gamma (programGraph (spineGuard measure) (suc z) xs))) :
    Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) sm).imp
        (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td sd))) := by
  let P := graph1 InternalUnpair.left (suc z) sm
  have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht := flagValue measure 0 sm xs (withHyp hsm P) hp
  have hboth := successorBranchElim (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (spineTest measure 0))
    (InternalLessThan.constantOne 4)
    (InternalAcceptance.conjunction (spineTest measure 1) (depthLess measure)) (suc z) z xs
    (normalizeAccept (spineTest measure 0) xs ht) (withHyp hg P)
  have factors := conjunctionRecover (spineTest measure 1) (depthLess measure) xs hboth
  obtain ⟨hf⟩ := flagRecover measure 1 tm xs (withHyp htm P) (andLeft factors)
  obtain ⟨hl⟩ := lessRecover measure sm tm sd td xs
    (withHyp hsm P) (withHyp htm P) (withHyp hsd P) (withHyp htd P) (andRight factors)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction hf hl)⟩

theorem spineValue (measure : Program 1) (sm tm sd td : OTerm α) (xs : Fin 4 → OTerm α)
    (hsm : Nonempty (Derivation body Gamma (graph1 measure sm (xs 0))))
    (htm : Nonempty (Derivation body Gamma (graph1 measure tm (xs 1))))
    (hsd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right sd sm)))
    (htd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm)))
    (hc : Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) sm).imp
        (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td sd)))) :
    Nonempty (Derivation body Gamma (programGraph (spineGuard measure) (suc z) xs)) := by
  apply formulaCases (graph1 InternalUnpair.left (suc z) sm)
  · let P := graph1 InternalUnpair.left (suc z) sm
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hc'⟩ := withHyp hc P
    have hboth : Nonempty (Derivation body (P :: Gamma)
        (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td sd)) :=
      ⟨Derivation.implicationElimination hc' (Derivation.hypothesis List.mem_cons_self)⟩
    have ht := flagValue measure 0 sm xs (withHyp hsm P) hp
    have hout := conjunctionAccept (spineTest measure 1) (depthLess measure) xs
      (flagValue measure 1 tm xs (withHyp htm P) (andLeft hboth))
      (lessValue measure sm tm sd td xs (withHyp hsm P) (withHyp htm P)
        (withHyp hsd P) (withHyp htd P) (andRight hboth))
    exact successorBranchIntro (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (spineTest measure 0))
      (InternalLessThan.constantOne 4)
      (InternalAcceptance.conjunction (spineTest measure 1) (depthLess measure)) (suc z) z xs
      (normalizeAccept (spineTest measure 0) xs ht) hout
  · let P := (graph1 InternalUnpair.left (suc z) sm).not
    have hp : Nonempty (Derivation body (P :: Gamma) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hn := testReject measure 0 sm xs (withHyp hsm P) hp
    exact zeroBranchIntro (LogicLineages.ComputabilityKnowledge.GorbowVerifierNormalization.normalize (spineTest measure 0))
      (InternalLessThan.constantOne 4)
      (InternalAcceptance.conjunction (spineTest measure 1) (depthLess measure)) (suc z) xs
      (normalizeReject (spineTest measure 0) xs hn) (InternalLessThanSupportProof.oneConstantValue xs)

def marked {α : Type} (measure : Program 1) (x y sm tm sd td : OTerm α) : Formula α :=
  graph1 measure sm x ⊓ (graph1 measure tm y ⊓
    (graph1 InternalUnpair.right sd sm ⊓ graph1 InternalUnpair.right td tm))

def conditions {α : Type} (bottom : Program 1) (edge : Program 4)
    (x y certificate parameter sm tm sd td : OTerm α) : Formula α :=
  graph4 (InternalParameterizedPathChecker.checker edge true) (suc z) x y certificate parameter ⊓
    ((graph1 bottom (suc z) x).not ⊓
      ((graph1 InternalUnpair.left (suc z) sm).imp
        (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td sd)))

theorem recover (bottom measure : Program 1) (edge : Program 4)
    (x y certificate parameter sm tm sd td : OTerm α)
    (hm : Nonempty (Derivation body Gamma (marked measure x y sm tm sd td)))
    (ha : Nonempty (Derivation body Gamma (accepted bottom measure edge x y certificate parameter))) :
    Nonempty (Derivation body Gamma (conditions bottom edge x y certificate parameter sm tm sd td)) := by
  let xs : Fin 4 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have top := conjunctionRecover (nonBottomGuard bottom)
    (InternalAcceptance.conjunction (spineGuard measure) (InternalParameterizedPathChecker.checker edge true)) xs ha
  have tail := conjunctionRecover (spineGuard measure) (InternalParameterizedPathChecker.checker edge true)
    xs (andRight top)
  exact andIntro (andRight tail) (andIntro (nonBottomRecover bottom xs (andLeft top))
    (spineRecover measure sm tm sd td xs (andLeft hm) (andLeft (andRight hm))
      (andLeft (andRight (andRight hm))) (andRight (andRight (andRight hm))) (andLeft tail)))

theorem value (bottom measure : Program 1) (edge : Program 4)
    (x y certificate parameter sm tm sd td : OTerm α)
    (hm : Nonempty (Derivation body Gamma (marked measure x y sm tm sd td)))
    (hc : Nonempty (Derivation body Gamma (conditions bottom edge x y certificate parameter sm tm sd td))) :
    Nonempty (Derivation body Gamma (accepted bottom measure edge x y certificate parameter)) := by
  let xs : Fin 4 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  apply conjunctionAccept (nonBottomGuard bottom)
    (InternalAcceptance.conjunction (spineGuard measure) (InternalParameterizedPathChecker.checker edge true)) xs
    (nonBottomValue bottom xs (andLeft (andRight hc)))
  exact conjunctionAccept (spineGuard measure) (InternalParameterizedPathChecker.checker edge true) xs
    (spineValue measure sm tm sd td xs (andLeft hm) (andLeft (andRight hm))
      (andLeft (andRight (andRight hm))) (andRight (andRight (andRight hm))) (andRight (andRight hc)))
    (andLeft hc)

theorem actualPositiveGuardEquation : PositiveSpineRulesTargets.ActualPositiveGuardEquation := by
  intro body bottom measure edge α Delta x y certificate parameter sm tm sd td
  let H := marked measure x y sm tm sd td
  let P := accepted bottom measure edge x y certificate parameter
  let Q := conditions bottom edge x y certificate parameter sm tm sd td
  have hh : Derivation body (H :: Delta) H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨hf⟩ := recover bottom measure edge x y certificate parameter sm tm sd td
    ⟨addHyp hh P⟩ (show Nonempty (Derivation body (P :: H :: Delta) P) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := value bottom measure edge x y certificate parameter sm tm sd td
    ⟨addHyp hh Q⟩ (show Nonempty (Derivation body (Q :: H :: Delta) Q) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
      (Derivation.implicationIntroduction hb))⟩

theorem actualPositiveGuardNonBottom : PositiveSpineRulesTargets.ActualPositiveGuardNonBottom := by
  intro body bottom measure edge α Delta x y certificate parameter
  let P := accepted bottom measure edge x y certificate parameter
  let xs : Fin 4 → OTerm α := Fin.cons x (Fin.cons y (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  have hp : Nonempty (Derivation body (P :: Delta) P) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have htop := conjunctionRecover (nonBottomGuard bottom)
    (InternalAcceptance.conjunction (spineGuard measure) (InternalParameterizedPathChecker.checker edge true)) xs hp
  obtain ⟨hn⟩ := nonBottomRecover bottom xs (andLeft htop)
  exact ⟨Derivation.implicationIntroduction hn⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
