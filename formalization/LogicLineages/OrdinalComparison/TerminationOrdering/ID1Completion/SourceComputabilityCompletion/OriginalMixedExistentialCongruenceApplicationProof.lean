module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalExistentialRankResultApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceApplicationProof
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
open OriginalLambdaErasureSquareDichotomyDefinitions (Witness Certificate)
open OriginalLambdaErasureSquareDichotomySyntaxProof (witnessRename witnessIntro)
open OriginalExistentialRankResultDefinitions (Result RankWitness)
open OriginalMixedExistentialCongruenceSupportProof
open OriginalTransparentMixedDirectBottom (source leaf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalMixedExistentialCongruenceDefinitions
theorem frameRename {beta : Type} (source : Program 2)
 (s t parameter childS childT arg d e arrow : OTerm alpha) (j : alpha → beta) :
 (ApplicationFrame source s t parameter childS childT arg d e arrow).relabel j =
 ApplicationFrame source (s.relabel j) (t.relabel j) (parameter.relabel j) (childS.relabel j)
  (childT.relabel j) (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) := by
 simp only [ApplicationFrame,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
  InternalOriginalStepGuard.one,sucRelabel,zRelabel]

theorem equalParents (s t d e childS childT arg : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph4 application s d e childS arg)))
 (ht : Nonempty (Derivation body Delta (graph4 application t d e childT arg)))
 (he : Nonempty (Derivation body Delta (equal childS childT))) :
 Nonempty (Derivation body Delta (equal s t)) := by
 have hs' : Nonempty (Derivation body Delta (graph4 application s d e childT arg)) := by
  apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 4 Delta
   (OrdinaryArithmetic.graphFormula application) s ![d,e,childS,arg] ![d,e,childT,arg] _ hs
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) i
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact ⟨InternalTagArithmeticSupportProof.refl d⟩
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact ⟨InternalTagArithmeticSupportProof.refl e⟩
  · change Nonempty (Derivation body Delta (equal childS childT))
    exact he
  · rw [InternalSourceInversionSupportProof.onEquality]
    exact ⟨InternalTagArithmeticSupportProof.refl arg⟩
 obtain ⟨hout⟩ := valueUnique application s t ![d,e,childT,arg] hs' ht
 exact ⟨by simpa only [equalEqn] using hout⟩

theorem frameHop (source : Program 2)
 (s t parameter childS childT arg d e arrow cert childCert : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (ApplicationFrame source s t parameter childS childT arg d e arrow)))
 (hp : Nonempty (Derivation body Delta (graph1 stepLift cert childCert))) :
 Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop source
  s t cert parameter childS childT childCert arg d e arrow)) := by
 have h1 := andRight hf
 have h2 := andRight h1
 have h3 := andRight h2
 have h4 := andRight h3
 have h5 := andRight h4
 exact andIntro (andLeft hf) (andIntro (andLeft h1) (andIntro (andLeft h2)
  (andIntro (andLeft h3) (andIntro (andLeft h4) (andIntro (andLeft h5) (andIntro (andRight h5) hp))))))

theorem fromCertificate (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t parameter childS childT arg d e arrow childCert : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (ApplicationFrame (source H G M W) s t parameter childS childT arg d e arrow)))
 (hc : Nonempty (Derivation body Delta (Certificate (leaf H G M W oldStep) childS childT parameter childCert))) :
 Nonempty (Derivation body Delta (Witness (leaf H G M W oldStep) s t parameter)) := by
 apply programCases stepLift (Fin.cons childCert Fin.elim0) _
 intro beta j Theta cert hj hp
 rw [witnessRename]
 simp only [consTermRename,emptyRename] at hp
 have hf' := renameInto hf j Theta hj
 rw [frameRename] at hf'
 have hc' := renameInto hc j Theta hj
 simp only [Certificate,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hc'
 have hh := frameHop (source H G M W)
  (s.relabel j) (t.relabel j) (parameter.relabel j) (childS.relabel j) (childT.relabel j)
  (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) cert (childCert.relabel j) hf' hp
 obtain ⟨law⟩ := OriginalTransparentMixedPathApplicationPrefixProof.hop (source H G M W)
  (OriginalTransparentDirectBottom.refined (source H G M W) oldStep)
  (s.relabel j) (t.relabel j) cert (parameter.relabel j) (childS.relabel j) (childT.relabel j) (childCert.relabel j)
  (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) InternalOriginalStepGuard.one hh
 obtain ⟨hc'⟩ := hc'
 exact witnessIntro (leaf H G M W oldStep) (s.relabel j) (t.relabel j) (parameter.relabel j) cert
  ⟨Derivation.implicationElimination (Derivation.conjunctionRight law) hc'⟩

theorem actualApplication : OriginalMixedExistentialCongruenceTargets.ActualApplication := by
 intro H G M W oldStep body alpha Delta s t parameter childS childT arg d e arrow oldS oldT oldChildS oldChildT oldArg hf hs ht hresult
 let L := leaf H G M W oldStep
 let A := equal childS childT ⊓ RankWitness oldChildS oldChildT
 let B := Witness L childS childT parameter
 have left : Nonempty (Derivation body (A :: Delta) (Result L s t parameter oldS oldT)) := by
  have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have he := equalParents s t d e childS childT arg
   (withHyp (andLeft (andRight hf)) A) (withHyp (andLeft (andRight (andRight hf))) A) (andLeft ha)
  have hr := OriginalExistentialRankResultApplicationProof.lift oldS oldT d e oldChildS oldChildT oldArg
   (withHyp hs A) (withHyp ht A) (andRight ha)
  obtain ⟨out⟩ := andIntro he hr
  exact ⟨orLeft out⟩
 have right : Nonempty (Derivation body (B :: Delta) (Result L s t parameter oldS oldT)) := by
  have hb : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hw : Nonempty (Derivation body (B :: Delta) (Witness L s t parameter)) := by
   apply mapWitness L s t parameter childS childT parameter hb
   intro beta j Theta cert hj hc
   have hf' := renameInto (withHyp hf B) j Theta hj
   rw [frameRename] at hf'
   exact fromCertificate H G M W oldStep (s.relabel j) (t.relabel j) (parameter.relabel j)
    (childS.relabel j) (childT.relabel j) (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j) cert hf' hc
  obtain ⟨hw⟩ := hw
  exact ⟨orRight hw⟩
 obtain ⟨hresult⟩ := hresult
 obtain ⟨left⟩ := left
 obtain ⟨right⟩ := right
 exact ⟨disjunctionElimination hresult (Derivation.implicationIntroduction left) (Derivation.implicationIntroduction right)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceApplicationProof
