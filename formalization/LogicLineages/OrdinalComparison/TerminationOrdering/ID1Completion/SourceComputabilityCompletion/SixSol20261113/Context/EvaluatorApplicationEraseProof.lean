module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalApplicationValidityClosure
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransport OriginalPackedApplicationErasureProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem actualApplicationErase : EvaluatorApplicationEraseTargets.ActualApplicationErase := by
 intro body alpha Delta arrow d e fp ap fn arg parent parentOut fnOut argOut erasedType cutoff psi hc hp hf ha k
 let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
 let xs : Fin 2 → OTerm alpha := ![fnOut,argOut]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs psi
 intro beta j Theta values hj hg
 have hx : (fun i => (xs i).relabel j) =
     (![fnOut.relabel j,argOut.relabel j] : Fin 2 → OTerm beta) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i
 rw [hx] at hg
 let xx : Fin 2 → OTerm beta := ![fnOut.relabel j,argOut.relabel j]
 have hfr := unaryRecover InternalUnpair.right (.projection 0) (values 0) (fnOut.relabel j)
   xx (hg 0) (projectionValue 0 xx)
 have har := unaryRecover InternalUnpair.right (.projection 1) (values 1) (argOut.relabel j)
   xx (hg 1) (projectionValue 1 xx)
 have hc' := renameInto hc j Theta hj
 have hp' := renameInto hp j Theta hj
 have hf' := renameInto hf j Theta hj
 have ha' := renameInto ha j Theta hj
 simp only [applicationConstructors,conjunctionRename,graph2Rename,graph4Rename] at hc'
 rw [graph3Rename] at hp' hf' ha'
 have hfn := andLeft (andRight hc')
 have harg := andLeft (andRight (andRight hc'))
 have happ := applicationBackward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
   (fp.relabel j) (ap.relabel j) (parent.relabel j)
   (pairRight (fn.relabel j) (arrow.relabel j) (fp.relabel j) hfn)
   (pairRight (arg.relabel j) (d.relabel j) (ap.relabel j) harg)
   (andRight (andRight (andRight hc')))
 have hout := applicationErasure (parent.relabel j) (d.relabel j) (e.relabel j)
   (fn.relabel j) (arg.relabel j) (parentOut.relabel j) (fnOut.relabel j) (argOut.relabel j)
   (erasedType.relabel j) (cutoff.relabel j) happ hp' hf' ha'
 have hft := eraseTypeCopy (fn.relabel j) (fnOut.relabel j) (arrow.relabel j)
   (erasedType.relabel j) (cutoff.relabel j)
   (pairLeft (fn.relabel j) (arrow.relabel j) (fp.relabel j) hfn) hf'
 have hat := eraseTypeCopy (arg.relabel j) (argOut.relabel j) (d.relabel j)
   (erasedType.relabel j) (cutoff.relabel j)
   (pairLeft (arg.relabel j) (d.relabel j) (ap.relabel j) harg) ha'
 apply k beta j Theta hj (values 0) (values 1)
 exact andIntro (andLeft hc') (andIntro
   (reconstructPair (fnOut.relabel j) (arrow.relabel j) (values 0) hft hfr)
   (andIntro (reconstructPair (argOut.relabel j) (d.relabel j) (values 1) hat har)
     (applicationForward (d.relabel j) (e.relabel j) (fnOut.relabel j) (argOut.relabel j)
       (values 0) (values 1) (parentOut.relabel j) hfr har hout)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorApplicationEraseProof
