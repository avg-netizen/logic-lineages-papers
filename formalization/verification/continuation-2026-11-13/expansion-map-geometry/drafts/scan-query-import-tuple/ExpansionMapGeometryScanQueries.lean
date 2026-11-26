module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalTagArithmeticSupportProof (symm addZero addSucc)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion (lengthGraph)
open ExpansionMapGeometryScanDefinitions ExpansionMapGeometryScanSyntax ExpansionMapGeometryScanRowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
theorem withSuffix (count start role typ raw jobs prefixRow full previous suffix : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan previous (add start count) role typ raw jobs)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start (suc count)) role typ raw jobs)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count suffix)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append previous prefixRow suffix))) :
 Nonempty (Derivation body Delta (Extension (suc count) prefixRow full)) := by
 let cp : Program 6 := .composition OriginalHereditaryInternalAnnotatedScanDefinitions.cell
   ![.projection 0,.projection 1,.projection 2,.projection 3,.projection 4]
 let sp : Program 6 := consOf cp (OriginalRawSyntaxTransport.constant 6 0)
 let gp : Program 6 := .composition InternalApplicationValidityStackAppend.append ![.projection 5,sp]
 let lp : Program 6 := .composition InternalRawListRecursion.lookup ![.projection 0,.projection 4]
 let qs : Fin 4 → Program 6 := ![cp,sp,gp,lp]
 let xs : Fin 6 → OTerm alpha := ![add start count,role,typ,raw,jobs,suffix]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs _
 intro beta j Theta ys hinc hq
 let xx : Fin 6 → OTerm beta := ![add (start.relabel j) (count.relabel j),role.relabel j,typ.relabel j,raw.relabel j,jobs.relabel j,suffix.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   simp only [xs,xx,InternalOriginalOrderSyntaxProof.addRelabel]
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
 rw [hx] at hq
 have hp' := renameInto hp j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have ha' := renameInto ha j Theta hinc
 simp only [graph5Rename,graph2Rename,OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel,sucRelabel] at hp' hf' hl' ha'
 have hm : Nonempty (Derivation body Theta
   (graph5 OriginalHereditaryInternalAnnotatedScanDefinitions.cell (ys 0)
     (add (start.relabel j) (count.relabel j)) (role.relabel j) (typ.relabel j) (raw.relabel j) (jobs.relabel j))) := by
   apply compositionRecover OriginalHereditaryInternalAnnotatedScanDefinitions.cell _ (ys 0) xx
     ![add (start.relabel j) (count.relabel j),role.relabel j,typ.relabel j,raw.relabel j,jobs.relabel j] (hq 0)
   intro i
   exact Fin.cases (projectionValue 0 xx) (Fin.cases (projectionValue 1 xx)
     (Fin.cases (projectionValue 2 xx) (Fin.cases (projectionValue 3 xx) (Fin.cases (projectionValue 4 xx) (fun k => Fin.elim0 k))))) i
 have hs := binaryRecover InternalListCodec.consCode cp (OriginalRawSyntaxTransport.constant 6 0)
   (ys 1) (ys 0) z xx (hq 1) (hq 0) (OriginalRawSyntaxTransportInternalVariableSupportProof.constantValue 0 xx)
 have hg := binaryRecover InternalApplicationValidityStackAppend.append (.projection 5) sp
   (ys 2) (suffix.relabel j) (ys 1) xx (hq 2) (projectionValue 5 xx) (hq 1)
 have hr := binaryRecover InternalRawListRecursion.lookup (.projection 0) (.projection 4)
   (ys 3) (add (start.relabel j) (count.relabel j)) (jobs.relabel j) xx (hq 3) (projectionValue 0 xx) (projectionValue 4 xx)
 rw [extensionRename,sucRelabel]
 exact ExpansionMapGeometryScanCore.atValues (count.relabel j) (start.relabel j) (role.relabel j)
   (typ.relabel j) (raw.relabel j) (jobs.relabel j) (prefixRow.relabel j) (full.relabel j)
   (previous.relabel j) (suffix.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) hp' hf' hl' ha' hm hs hg hr

theorem withPrevious (count start role typ raw jobs prefixRow full previous : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count start role typ raw jobs prefixRow)))
 (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan previous (add start count) role typ raw jobs)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start (suc count)) role typ raw jobs))) :
 Nonempty (Derivation body Delta (Extension (suc count) prefixRow full)) := by
 have he := rowApply count start role typ raw jobs prefixRow previous hi hp
 apply extensionCases count prefixRow previous _ he
 intro beta j Theta suffix hinc hs
 have hp' := renameInto hp j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [graph5Rename,InternalOriginalOrderSyntaxProof.addRelabel,sucRelabel] at hp' hf'
 rw [extensionRename,sucRelabel]
 exact withSuffix (count.relabel j) (start.relabel j) (role.relabel j) (typ.relabel j)
   (raw.relabel j) (jobs.relabel j) (prefixRow.relabel j) (full.relabel j) (previous.relabel j) suffix
   hp' hf' (andLeft hs) (andRight hs)

theorem successorCore (count start role typ raw jobs prefixRow full : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row count start role typ raw jobs prefixRow)))
 (hf : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan full (add start (suc count)) role typ raw jobs))) :
 Nonempty (Derivation body Delta (Extension (suc count) prefixRow full)) := by
 apply InternalAcceptanceSupportProof.programCases OriginalHereditaryAnnotatedExpansion.scan
   ![add start count,role,typ,raw,jobs] _
 intro beta j Theta previous hinc hp
 have hi' := renameInto hi j Theta hinc
 have hf' := renameInto hf j Theta hinc
 simp only [rowRename,graph5Rename,InternalOriginalOrderSyntaxProof.addRelabel,sucRelabel] at hi' hf'
 simp only [consTermRename,InternalRecursionGraphStepSyntaxProof.emptyRename,InternalOriginalOrderSyntaxProof.addRelabel] at hp
 rw [extensionRename,sucRelabel]
 exact withPrevious (count.relabel j) (start.relabel j) (role.relabel j) (typ.relabel j)
   (raw.relabel j) (jobs.relabel j) (prefixRow.relabel j) (full.relabel j) previous hi' hp hf'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryScanQueries
