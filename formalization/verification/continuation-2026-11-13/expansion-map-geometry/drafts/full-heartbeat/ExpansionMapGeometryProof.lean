module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion (lengthGraph)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open InternalAcceptanceSupportProof (programCases)
open ExpansionMapGeometryScanDefinitions ExpansionMapGeometryScanSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem partitionStrong (F : Program 1) (job role typ typed rawJob raw parameter c gamma children deletions jobs forward produced : OTerm alpha) (psi : Formula alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (lengthGraph deletions gamma)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) forward jobs)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (rawJobs annotatedPrefix childRow backwardChildren deletionPrefix annotatedSuffix suffixForward : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (ExpansionMapGeometryDefinitions.Geometry F
     (role.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j)
     (children.relabel j) (deletions.relabel j) (produced.relabel j)
     rawJobs annotatedPrefix childRow backwardChildren deletionPrefix)) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append
     (jobs.relabel j) annotatedPrefix annotatedSuffix)) →
   Nonempty (Derivation body Theta (graph1 (InternalListMap.map (k := 0) F) suffixForward annotatedSuffix)) →
   Nonempty (Derivation body Theta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix suffixForward)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 apply programCases OriginalHereditaryExpansion.expansion ![raw,parameter] psi
 intro beta j Theta rawJobs hinc hraw
 have hx : (fun i => (![raw,parameter] i).relabel j) = ![raw.relabel j,parameter.relabel j] := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hraw
 have hj' := renameInto hj j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hr' := renameInto hr j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have he' := renameInto he j Theta hinc
 have hm' := renameInto hm j Theta hinc
 have hv' := renameInto hv j Theta hinc
 simp only [graph1Rename,graph2Rename,OriginalContextInsertionSyntaxProof.lengthRename] at hj' ht' hr' hp' ha' hl' he' hm' hv'
 have hrawlen := SourceFramedRawExpansionLengthProof.rawLength (raw.relabel j) (parameter.relabel j)
   (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) rawJobs ha' hp' hl' hraw
 have hdecorate := SourceFramedExpansionLengthProof.decorateRecover (role.relabel j) (typ.relabel j)
   (raw.relabel j) (parameter.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) rawJobs (jobs.relabel j)
   hr' ht' hj' hraw he'
 have hfull := SixSol20261113.Context.NarrowScanRecoverProof.scanFromAll (role.relabel j) (typ.relabel j)
   (raw.relabel j) rawJobs (jobs.relabel j) (add (children.relabel j) (deletions.relabel j)) hdecorate hrawlen
 apply programCases OriginalHereditaryAnnotatedExpansion.scan
   ![children.relabel j,role.relabel j,typ.relabel j,raw.relabel j,rawJobs] _
 intro gammaType k Xi prefixRow hk hprefix
 have hx2 : (fun i => (![children.relabel j,role.relabel j,typ.relabel j,raw.relabel j,rawJobs] i).relabel k) =
   ![(children.relabel j).relabel k,(role.relabel j).relabel k,(typ.relabel j).relabel k,(raw.relabel j).relabel k,rawJobs.relabel k] := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))))) i
 rw [hx2] at hprefix
 have hfull2 := renameInto hfull k Xi hk
 have hraw2 := renameInto hraw k Xi hk
 have hm2 := renameInto hm' k Xi hk
 have hv2 := renameInto hv' k Xi hk
 simp only [graph5Rename,graph2Rename,graph1Rename,InternalOriginalOrderSyntaxProof.addRelabel] at hfull2 hraw2 hm2 hv2
 have hext := ExpansionMapGeometryScanProof.actualExtension body gammaType Xi
   ((children.relabel j).relabel k) ((deletions.relabel j).relabel k)
   ((role.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k)
   (rawJobs.relabel k) prefixRow ((jobs.relabel j).relabel k) hprefix hfull2
 apply extensionCases ((deletions.relabel j).relabel k) prefixRow ((jobs.relabel j).relabel k) _ hext
 intro omega l Omega suffix hlinc hsuffix
 have hprefix3 := renameInto hprefix l Omega hlinc
 have hfull3 := renameInto hfull2 l Omega hlinc
 have hraw3 := renameInto hraw2 l Omega hlinc
 have hm3 := renameInto hm2 l Omega hlinc
 have hv3 := renameInto hv2 l Omega hlinc
 simp only [graph5Rename,graph2Rename,graph1Rename,InternalOriginalOrderSyntaxProof.addRelabel] at hprefix3 hfull3 hraw3 hm3 hv3
 apply ExpansionMapGeometryRowsProof.atSuffix F
   (((children.relabel j).relabel k).relabel l) (((deletions.relabel j).relabel k).relabel l)
   (((role.relabel j).relabel k).relabel l) (((typ.relabel j).relabel k).relabel l)
   (((raw.relabel j).relabel k).relabel l) ((rawJobs.relabel k).relabel l) (prefixRow.relabel l)
   (((jobs.relabel j).relabel k).relabel l) (((forward.relabel j).relabel k).relabel l)
   (((produced.relabel j).relabel k).relabel l) suffix _
   hprefix3 hfull3 (andLeft hsuffix) (andRight hsuffix) hm3 hv3
 intro omega2 m Omega2 childRow backwardChildren deletionPrefix suffixForward hmInc
   hchildmap hchildlen hchildreverse hdellen hproduced htotal hsuffixmap hsuffixreverse
 have hraw4 := renameInto hraw3 m Omega2 hmInc
 have hprefix4 := renameInto hprefix3 m Omega2 hmInc
 have hsplit4 := renameInto (andRight hsuffix) m Omega2 hmInc
 simp only [graph2Rename,graph5Rename] at hraw4 hprefix4 hsplit4
 have inc : ∀ f ∈ Delta, f.relabel (m ∘ l ∘ k ∘ j) ∈ Omega2 := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hmInc _ (hlinc _ (hk _ (hinc f hf)))
 have hg := andIntro hraw4 (andIntro hprefix4 (andIntro hchildmap (andIntro hchildlen
   (andIntro hchildreverse (andIntro hdellen (andIntro hproduced htotal))))))
 have out := next omega2 (m ∘ l ∘ k ∘ j) Omega2
   (((rawJobs.relabel k).relabel l).relabel m) ((prefixRow.relabel l).relabel m)
   childRow backwardChildren deletionPrefix (suffix.relabel m) suffixForward inc
   (by simpa only [ExpansionMapGeometryDefinitions.Geometry,Term.relabel_relabel] using hg)
   (by simpa only [Term.relabel_relabel] using hsplit4) hsuffixmap hsuffixreverse
 simpa only [formulaRelabelComposition] using out

theorem actualPartition : ExpansionMapGeometryTargets.ActualPartition := by
 intro F body alpha Delta job role typ typed rawJob raw parameter c gamma children deletions jobs forward produced psi
   hj ht hr hp ha hl he hm hv next
 apply partitionStrong F job role typ typed rawJob raw parameter c gamma children deletions jobs forward produced psi
   hj ht hr hp ha hl he hm hv
 intro beta j Theta rawJobs annotatedPrefix childRow backwardChildren deletionPrefix annotatedSuffix suffixForward hinc hg _ _ _
 exact next beta j Theta rawJobs annotatedPrefix childRow backwardChildren deletionPrefix hinc hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryProof
