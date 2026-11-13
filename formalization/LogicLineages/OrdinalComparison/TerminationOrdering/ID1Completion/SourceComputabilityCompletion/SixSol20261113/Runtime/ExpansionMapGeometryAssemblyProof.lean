module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryAssemblyProof
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
theorem atPrefix (F : Program 1)
 (role typ raw parameter children deletions jobs forward produced rawJobs prefixRow : OTerm alpha) (psi : Formula alpha)
 (hraw : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (hprefix : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefixRow children role typ raw rawJobs)))
 (hfull : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan jobs (add children deletions) role typ raw rawJobs)))
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
 have hext := ExpansionMapGeometryScanProof.actualExtension body alpha Delta
   children deletions
   role typ raw
   rawJobs prefixRow jobs hprefix hfull
 apply extensionCases deletions prefixRow jobs _ hext
 intro omega l Omega suffix hlinc hsuffix
 have hprefix3 := renameInto hprefix l Omega hlinc
 have hfull3 := renameInto hfull l Omega hlinc
 have hraw3 := renameInto hraw l Omega hlinc
 have hm3 := renameInto hm l Omega hlinc
 have hv3 := renameInto hv l Omega hlinc
 simp only [graph5Rename,graph2Rename,graph1Rename,InternalOriginalOrderSyntaxProof.addRelabel] at hprefix3 hfull3 hraw3 hm3 hv3
 apply ExpansionMapGeometryRowsProof.atSuffix F
   (children.relabel l) (deletions.relabel l)
   (role.relabel l) (typ.relabel l)
   (raw.relabel l) (rawJobs.relabel l) (prefixRow.relabel l)
   (jobs.relabel l) (forward.relabel l)
   (produced.relabel l) suffix _
   hprefix3 hfull3 (andLeft hsuffix) (andRight hsuffix) hm3 hv3
 intro omega2 m Omega2 childRow backwardChildren deletionPrefix suffixForward hmInc
   hchildmap hchildlen hchildreverse hdellen hproduced htotal hsuffixmap hsuffixreverse
 have hraw4 := renameInto hraw3 m Omega2 hmInc
 have hprefix4 := renameInto hprefix3 m Omega2 hmInc
 have hsplit4 := renameInto (andRight hsuffix) m Omega2 hmInc
 simp only [graph2Rename,graph5Rename] at hraw4 hprefix4 hsplit4
 have inc : ∀ f ∈ Delta, f.relabel (m ∘ l) ∈ Omega2 := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hmInc _ (hlinc f hf)
 have hg := andIntro hraw4 (andIntro hprefix4 (andIntro hchildmap (andIntro hchildlen
   (andIntro hchildreverse (andIntro hdellen (andIntro hproduced htotal))))))
 have out := next omega2 (m ∘ l) Omega2
   ((rawJobs.relabel l).relabel m) ((prefixRow.relabel l).relabel m)
   childRow backwardChildren deletionPrefix (suffix.relabel m) suffixForward inc
   (by simpa only [ExpansionMapGeometryDefinitions.Geometry,Term.relabel_relabel] using hg)
   (by simpa only [Term.relabel_relabel] using hsplit4) hsuffixmap hsuffixreverse
 simpa only [formulaRelabelComposition] using out
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryAssemblyProof
