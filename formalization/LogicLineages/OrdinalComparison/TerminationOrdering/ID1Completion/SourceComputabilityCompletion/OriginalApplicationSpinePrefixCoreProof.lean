module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem successorLess (x y : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ltF x y))) :
 Nonempty (Derivation body Delta (ltF (suc x) (suc y))) := by
 apply InternalOriginalOrderProof.orderCases Delta x y _ h
 intro beta j Theta gap incl he
 simp only [orderRename,sucRelabel]
 obtain ⟨he⟩ := he
 apply InternalOriginalOrderProof.actualOriginalOrderIntroduction body beta Theta (suc (x.relabel j)) (suc (y.relabel j)) gap
 rw [InternalSourceInversionSupportProof.onEquality]
 exact ⟨InternalTagArithmeticSupportProof.trans
  (InternalAdditionLawsProof.leftSuccessor (x.relabel j) (suc gap))
  (InternalTagArithmeticSupportProof.congSuc he)⟩

theorem atMarks (s t cert childCert parameter fn targetFn sm tm sf tf sd td pm qm : OTerm alpha)
 (hsm : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure sm fn)))
 (htm : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure tm targetFn)))
 (hsf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left sf sm)))
 (htf : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tf tm)))
 (hsd : Nonempty (Derivation body Delta (graph1 InternalUnpair.right sd sm)))
 (htd : Nonempty (Derivation body Delta (graph1 InternalUnpair.right td tm)))
 (hpm : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure pm s)))
 (hqm : Nonempty (Derivation body Delta (graph1 BottomSpineMeasure.measure qm t)))
 (hpp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing pm sf (suc sd))))
 (hqp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing qm tf (suc td))))
 (hg : Nonempty (Derivation body Delta (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  (suc z) fn targetFn childCert parameter))) :
 Nonempty (Derivation body Delta (graph4 (UniformCertificateCompletion.PositiveGuard.spineGuard BottomSpineMeasure.measure)
  (suc z) s t cert parameter)) := by
 have hi := PositiveSpineRulesProof.spineRecover BottomSpineMeasure.measure sm tm sd td
  ![fn,targetFn,childCert,parameter] hsm htm hsd htd hg
 let A := graph1 InternalUnpair.left (suc z) pm
 have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 have hsf1 := valueUnique InternalUnpair.left sf (suc z) ![pm]
  (withHyp (pairLeft pm sf (suc sd) hpp) A) hA
 have hchildFlag := outputTransport InternalUnpair.left sf (suc z) ![sm] hsf1 (withHyp hsf A)
 obtain ⟨hi'⟩ := withHyp hi A
 obtain ⟨hchildFlag⟩ := hchildFlag
 have hboth := (show Nonempty (Derivation body (A :: Delta)
  (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td sd)) from
   ⟨Derivation.implicationElimination hi' hchildFlag⟩)
 have htf1 := valueUnique InternalUnpair.left tf (suc z) ![tm] (withHyp htf A) (andLeft hboth)
 have hparentFlag := outputTransport InternalUnpair.left tf (suc z) ![qm] htf1
  (withHyp (pairLeft qm tf (suc td) hqp) A)
 obtain ⟨hconditions⟩ := andIntro hparentFlag (successorLess td sd (andRight hboth))
 exact PositiveSpineRulesProof.spineValue BottomSpineMeasure.measure pm qm (suc sd) (suc td)
  ![s,t,cert,parameter] hpm hqm (pairRight pm sf (suc sd) hpp) (pairRight qm tf (suc td) hqp)
  ⟨Derivation.implicationIntroduction hconditions⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSpinePrefixCoreProof
