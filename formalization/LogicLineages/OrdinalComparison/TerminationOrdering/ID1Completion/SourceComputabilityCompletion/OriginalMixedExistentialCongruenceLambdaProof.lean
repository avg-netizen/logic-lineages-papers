module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathLambdaPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalLambdaErasureSquareDichotomyDefinitions (Witness Certificate Frame)
open OriginalLambdaErasureSquareDichotomySyntaxProof (witnessRename witnessIntro frameRename)
open OriginalExistentialRankResultDefinitions (Result RankWitness)
open OriginalMixedExistentialCongruenceSupportProof
open OriginalTransparentMixedDirectBottom (source leaf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fromCertificate (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t parameter childS childT childParam d e context gamma extended childCert : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (Frame (source H G M W) s t parameter childS childT childParam d e context gamma extended)))
 (hc : Nonempty (Derivation body Delta (Certificate (leaf H G M W oldStep) childS childT childParam childCert))) :
 Nonempty (Derivation body Delta (Witness (leaf H G M W oldStep) s t parameter)) := by
 apply programCases OriginalHereditaryLambda.prefixCertificate (Fin.cons childCert Fin.elim0) _
 intro beta j Theta cert hj hp
 rw [witnessRename]
 simp only [consTermRename,emptyRename] at hp
 have hf' := renameInto hf j Theta hj
 rw [frameRename] at hf'
 have hc' := renameInto hc j Theta hj
 simp only [Certificate,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hc'
 have hh := OriginalLambdaErasureSquareDichotomyProof.frameHop (source H G M W)
  (s.relabel j) (t.relabel j) (parameter.relabel j) (childS.relabel j) (childT.relabel j) (childParam.relabel j)
  (d.relabel j) (e.relabel j) (context.relabel j) (gamma.relabel j) (extended.relabel j) cert (childCert.relabel j) hf' hp
 obtain ⟨law⟩ := OriginalTransparentMixedPathLambdaPrefixProof.hop (source H G M W)
  (OriginalTransparentDirectBottom.refined (source H G M W) oldStep)
  (s.relabel j) (t.relabel j) cert (parameter.relabel j) (childS.relabel j) (childT.relabel j) (childCert.relabel j)
  (childParam.relabel j) (d.relabel j) (e.relabel j) (context.relabel j) (gamma.relabel j) (extended.relabel j)
  InternalOriginalStepGuard.one hh
 obtain ⟨hc'⟩ := hc'
 exact witnessIntro (leaf H G M W oldStep) (s.relabel j) (t.relabel j) (parameter.relabel j) cert
  ⟨Derivation.implicationElimination (Derivation.conjunctionRight law) hc'⟩

theorem actualLambda : OriginalMixedExistentialCongruenceTargets.ActualLambda := by
 intro H G M W oldStep body alpha Delta s t parameter childS childT childParam d e context gamma extended oldS oldT oldChildS oldChildT hf hs ht hresult
 let L := leaf H G M W oldStep
 let A := equal childS childT ⊓ RankWitness oldChildS oldChildT
 let B := Witness L childS childT childParam
 have left : Nonempty (Derivation body (A :: Delta) (Result L s t parameter oldS oldT)) := by
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he := OriginalLambdaErasureSquareDichotomyProof.equalParents s t d e childS childT
   (withHyp (andLeft (andRight hf)) A) (withHyp (andLeft (andRight (andRight hf))) A) (andLeft ha)
  have hr := OriginalExistentialRankResultLambdaProof.lift oldS oldT d e oldChildS oldChildT (withHyp hs A) (withHyp ht A) (andRight ha)
  obtain ⟨out⟩ := andIntro he hr
  exact ⟨orLeft out⟩
 have right : Nonempty (Derivation body (B :: Delta) (Result L s t parameter oldS oldT)) := by
  have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw : Nonempty (Derivation body (B :: Delta) (Witness L s t parameter)) := by
   apply mapWitness L s t parameter childS childT childParam hb
   intro beta j Theta cert hj hc
   have hf' := renameInto (withHyp hf B) j Theta hj
   rw [frameRename] at hf'
   exact fromCertificate H G M W oldStep (s.relabel j) (t.relabel j) (parameter.relabel j)
    (childS.relabel j) (childT.relabel j) (childParam.relabel j) (d.relabel j) (e.relabel j)
    (context.relabel j) (gamma.relabel j) (extended.relabel j) cert hf' hc
  obtain ⟨hw⟩ := hw
  exact ⟨orRight hw⟩
 obtain ⟨hresult⟩ := hresult
 obtain ⟨left⟩ := left
 obtain ⟨right⟩ := right
 exact ⟨disjunctionElimination hresult (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceLambdaProof
