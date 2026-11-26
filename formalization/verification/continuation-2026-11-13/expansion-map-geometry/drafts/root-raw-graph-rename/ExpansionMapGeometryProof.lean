module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryAssemblyProof
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
attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.scan InternalListMap.map

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
 apply ExpansionMapGeometryAssemblyProof.atPrefix F
   ((role.relabel j).relabel k) ((typ.relabel j).relabel k) ((raw.relabel j).relabel k)
   ((parameter.relabel j).relabel k) ((children.relabel j).relabel k) ((deletions.relabel j).relabel k)
   ((jobs.relabel j).relabel k) ((forward.relabel j).relabel k) ((produced.relabel j).relabel k)
   (rawJobs.relabel k) prefixRow _ hraw2 hprefix hfull2 hm2 hv2
 intro omega l Omega rawJobs3 prefix3 childRow backwardChildren deletionPrefix suffix suffixForward hinc3 hg hsplit hmap hreverse
 have inc : ∀ f ∈ Delta, f.relabel (l ∘ k ∘ j) ∈ Omega := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hinc3 _ (hk _ (hinc f hf))
 have out := next omega (l ∘ k ∘ j) Omega rawJobs3 prefix3 childRow backwardChildren deletionPrefix suffix suffixForward inc
   (by simpa only [Term.relabel_relabel] using hg)
   (by simpa only [Term.relabel_relabel] using hsplit) hmap hreverse
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
