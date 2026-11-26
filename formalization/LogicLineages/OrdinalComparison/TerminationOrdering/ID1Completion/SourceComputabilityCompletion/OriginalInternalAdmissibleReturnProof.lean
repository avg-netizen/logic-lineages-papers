module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open OriginalInternalAdmissibleReturnTargets
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualReturn : ActualReturn := by
 intro R body H M W alpha Delta input work results frame rest payload parent counts role typed typ rawJob raw parameter c gamma psi
   hs hw hf hp hpar hty hr hpctx ha next
 have coords := OriginalInternalAdmissibleReturnCoordinatesProof.coordinates input work results frame rest (numeral 1) payload parent counts role typed rawJob typ raw parameter
   hs hf hp hpar hty hr hw
 let qs : Fin 2 → Program 1 := ![InternalUnpair.left,InternalUnpair.right]
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 apply queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hpRaw := reconstructPair (raw.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
 have hs' := renameInto hs j Theta hj
 have hw' := renameInto hw j Theta hj
 have hf' := renameInto hf j Theta hj
 have ha' := renameInto ha j Theta hj
 have hrole := renameInto (andLeft coords) j Theta hj
 have hraw := renameInto (andRight coords) j Theta hj
 simp only [graph1Rename,graph2Rename,numeralRename,admissibleRename] at hs' hw' hf' ha' hrole hraw
 have hshape := OriginalInternalJobAdmissibleShapeProof.supportedReturn body H M W beta Theta
   (role.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) (ys 0) (ys 1) ha' hpRaw
 have htag := unaryValue InternalUnpair.left OriginalHereditaryReturnStep.raw (ys 0) (raw.relabel j)
   (Fin.cons (input.relabel j) Fin.elim0) (hq 0) hraw
 apply OriginalInternalAdmissibleReturnShapeProof.shapeCases R (input.relabel j) (work.relabel j) (results.relabel j)
   (frame.relabel j) (rest.relabel j) (payload.relabel j) (role.relabel j) (typ.relabel j) (ys 0) _
   hs' hw' hf' hrole htag hshape
 intro gammaType k Xi output stack hk hpair hstep
 have incl : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
   intro f hf
   simpa only [← formulaRelabelComposition] using hk _ (hj f hf)
 have hn := next gammaType (k ∘ j) Xi output stack incl
   (by simpa only [Term.relabel_relabel] using hpair)
   (by simpa only [Term.relabel_relabel] using hstep)
 simpa only [formulaRelabelComposition] using hn
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAdmissibleReturnProof
