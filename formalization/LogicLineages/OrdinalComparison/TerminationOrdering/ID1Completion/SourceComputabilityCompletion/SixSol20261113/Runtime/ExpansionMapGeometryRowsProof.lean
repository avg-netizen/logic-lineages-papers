module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseLengthInvolutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRowsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion (lengthGraph)
open ExpansionMapGeometryScanDefinitions ExpansionMapGeometryScanSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atSuffix (F : Program 1) (children deletions role typ raw rawJobs prefixRow jobs forward produced suffix : OTerm alpha) (psi : Formula alpha)
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan prefixRow children role typ raw rawJobs)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan jobs (add children deletions) role typ raw rawJobs)))
 (hs : Nonempty (Derivation body Delta (lengthGraph deletions suffix)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs prefixRow suffix)))
 (hm : Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) forward jobs)))
 (hr : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse produced forward)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (childRow backwardChildren deletionPrefix suffixForward : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 (InternalListMap.map (k := 0) F) childRow (prefixRow.relabel j))) →
   Nonempty (Derivation body Theta (lengthGraph (children.relabel j) childRow)) →
   Nonempty (Derivation body Theta (graph1 OriginalTypedArgumentObservations.reverse backwardChildren childRow)) →
   Nonempty (Derivation body Theta (lengthGraph (deletions.relabel j) deletionPrefix)) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append (produced.relabel j) deletionPrefix backwardChildren)) →
   Nonempty (Derivation body Theta (lengthGraph (add (children.relabel j) (deletions.relabel j)) (produced.relabel j))) →
   Nonempty (Derivation body Theta (graph1 (InternalListMap.map (k := 0) F) suffixForward (suffix.relabel j))) →
   Nonempty (Derivation body Theta (graph1 OriginalTypedArgumentObservations.reverse deletionPrefix suffixForward)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let mp : Program 2 := .composition (InternalListMap.map (k := 0) F) (fun _ : Fin 1 => .projection 0)
 let ms : Program 2 := .composition (InternalListMap.map (k := 0) F) (fun _ : Fin 1 => .projection 1)
 let rp : Program 2 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => mp)
 let rs : Program 2 := .composition OriginalTypedArgumentObservations.reverse (fun _ : Fin 1 => ms)
 let qs : Fin 4 → Program 2 := ![mp,rp,ms,rs]
 let xs : Fin 2 → OTerm alpha := ![prefixRow,suffix]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs psi
 intro beta j Theta ys hinc hq
 let xx : Fin 2 → OTerm beta := ![prefixRow.relabel j,suffix.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hp' := renameInto hp j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hs' := renameInto hs j Theta hinc
 have ha' := renameInto ha j Theta hinc
 have hm' := renameInto hm j Theta hinc
 have hr' := renameInto hr j Theta hinc
 simp only [graph5Rename,graph1Rename,graph2Rename,OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel] at hp' hf' hs' ha' hm' hr'
 have hmp := unaryRecover (InternalListMap.map (k := 0) F) (.projection 0)
   (ys 0) (prefixRow.relabel j) xx (hq 0) (projectionValue 0 xx)
 have hms := unaryRecover (InternalListMap.map (k := 0) F) (.projection 1)
   (ys 2) (suffix.relabel j) xx (hq 2) (projectionValue 1 xx)
 have hrp := unaryRecover OriginalTypedArgumentObservations.reverse mp (ys 1) (ys 0) xx (hq 1) (hq 0)
 have hrs := unaryRecover OriginalTypedArgumentObservations.reverse ms (ys 3) (ys 2) xx (hq 3) (hq 2)
 have hplen := SourceFramedScanLengthProof.scanLength (children.relabel j) (role.relabel j) (typ.relabel j)
   (raw.relabel j) (rawJobs.relabel j) (prefixRow.relabel j) hp'
 have hchildlen := MapLengthProof.actualMapLength F body beta Theta (children.relabel j) (prefixRow.relabel j) (ys 0) hplen hmp
 have hslen := MapLengthProof.actualMapLength F body beta Theta (deletions.relabel j) (suffix.relabel j) (ys 2) hs' hms
 have hdlen := andLeft (OriginalReverseLengthInvolutionProof.actualLaws body beta Theta (ys 2) (deletions.relabel j) (ys 3) hslen hrs)
 have hmapappend := ExpansionMapGeometryRecoverProof.mapAppendRecover F (prefixRow.relabel j) (suffix.relabel j)
   (jobs.relabel j) (ys 0) (ys 2) (forward.relabel j) ha' hmp hms hm'
 have hrevappend := ExpansionMapGeometryRecoverProof.reverseAppendRecover (ys 0) (ys 2) (forward.relabel j)
   (ys 1) (ys 3) (produced.relabel j) hmapappend hrp hrs hr'
 have hfullLen := SourceFramedScanLengthProof.scanLength (add (children.relabel j) (deletions.relabel j))
   (role.relabel j) (typ.relabel j) (raw.relabel j) (rawJobs.relabel j) (jobs.relabel j) hf'
 have hmLen := MapLengthProof.actualMapLength F body beta Theta (add (children.relabel j) (deletions.relabel j))
   (jobs.relabel j) (forward.relabel j) hfullLen hm'
 have hrLen := andLeft (OriginalReverseLengthInvolutionProof.actualLaws body beta Theta
   (forward.relabel j) (add (children.relabel j) (deletions.relabel j)) (produced.relabel j) hmLen hr')
 exact next beta j Theta (ys 0) (ys 1) (ys 3) (ys 2) hinc hmp hchildlen hrp hdlen hrevappend hrLen hms hrs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRowsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryRowsProof
