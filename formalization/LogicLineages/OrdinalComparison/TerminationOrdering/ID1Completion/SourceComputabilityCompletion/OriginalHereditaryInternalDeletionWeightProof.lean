module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalWeightDeletionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof InternalRecursionGraphStepSyntaxProof
open InternalOriginalOrderSyntaxProof
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalSquareRootArithmeticSupportProof (orderRight)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryInternalWeightDefinitions
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atCoordinates (parent child raw erased gamma deleted typ cutoff count W V : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (fields parent raw gamma)))
 (hc : Nonempty (Derivation body Delta (fields child erased deleted)))
 (he : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.eraseRaw erased typ cutoff raw)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
 (hb : Nonempty (Derivation body Delta (Below cutoff count)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff gamma)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight W parent)))
 (hv : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight V child))) :
 Nonempty (Derivation body Delta (ltF V W)) := by
 apply zeroSuccessorCases Delta count (ltF V W)
 · obtain ⟨hzero⟩ := (show Nonempty (Derivation body (eqn count z :: Delta) (eqn count z)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
   obtain ⟨hbound⟩ := weakenProof hb (fun f hf => List.mem_cons_of_mem _ hf)
   obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha cutoff
   exact ⟨Derivation.explosion (Derivation.implicationElimination (weakenClosed hn _) (orderRight cutoff hzero hbound))⟩
 · intro beta j Theta pred hj hcount
   let qs : Fin 2 → Program 2 := ![
     .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => .projection 0),
     .composition OriginalStructuralNodeSize.raw (fun _ : Fin 1 => .projection 1)]
   let xs : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (erased.relabel j) Fin.elim0)
   apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
   intro gamma' k ys Xi hk hq
   let xx : Fin 2 → OTerm gamma' := Fin.cons ((raw.relabel j).relabel k) (Fin.cons ((erased.relabel j).relabel k) Fin.elim0)
   have hq' : ∀ i, Nonempty (Derivation body Xi (programGraph (qs i) (ys i) xx)) := by
     intro i
     simpa only [xs,xx,consTermRename,emptyRename] using hq i
   have hbefore := unaryRecover OriginalStructuralNodeSize.raw (.projection 0) (ys 0) ((raw.relabel j).relabel k) xx (hq' 0) (projectionValue 0 xx)
   have hafter := unaryRecover OriginalStructuralNodeSize.raw (.projection 1) (ys 1) ((erased.relabel j).relabel k) xx (hq' 1) (projectionValue 1 xx)
   have incl : ∀ f ∈ Delta, f.relabel (k ∘ j) ∈ Xi := by
     intro f hf
     simpa only [← InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk _ (hj f hf)
   have hp' := renameInto hp (k ∘ j) Xi incl
   have hc' := renameInto hc (k ∘ j) Xi incl
   simp only [fields,conjunctionRename,graph1Rename] at hp' hc'
   have he' := renameInto he (k ∘ j) Xi incl
   rw [graph3Rename] at he'
   have hl' := renameInto hl (k ∘ j) Xi incl
   rw [lengthRename] at hl'
   have hb' := renameInto hb (k ∘ j) Xi incl
   simp only [Below,orderRename] at hb'
   have hd' := renameInto hd (k ∘ j) Xi incl
   rw [graph2Rename] at hd'
   have hw' := renameInto hw (k ∘ j) Xi incl
   have hv' := renameInto hv (k ∘ j) Xi incl
   rw [graph1Rename] at hw' hv'
   have hcount' := renameInto hcount k Xi hk
   simp only [eqnRename,sucRelabel,Term.relabel_relabel] at hcount'
   have hlength := outputTransport length (count.relabel (k ∘ j)) (suc (pred.relabel k))
     (Fin.cons (gamma.relabel (k ∘ j)) Fin.elim0) hcount' hl'
   obtain ⟨hcount'⟩ := hcount'
   obtain ⟨hb'⟩ := hb'
   have hbound : Nonempty (Derivation body Xi (Below (cutoff.relabel (k ∘ j)) (suc (pred.relabel k)))) :=
     ⟨orderRight (cutoff.relabel (k ∘ j)) hcount' hb'⟩
   have result := OriginalHereditaryInternalWeightDeletionProof.deletion body gamma' Xi
     (parent.relabel (k ∘ j)) (child.relabel (k ∘ j)) (raw.relabel (k ∘ j))
     (erased.relabel (k ∘ j)) (gamma.relabel (k ∘ j)) (deleted.relabel (k ∘ j))
     (typ.relabel (k ∘ j)) (cutoff.relabel (k ∘ j)) (pred.relabel k) (ys 0) (ys 1)
     (W.relabel (k ∘ j)) (V.relabel (k ∘ j)) hp' hc' he'
     (by simpa only [Term.relabel_relabel] using hbefore)
     (by simpa only [Term.relabel_relabel] using hafter) hlength hbound hd' hw' hv'
   simpa only [orderRename,Term.relabel_relabel] using result

theorem actualDecrease : OriginalHereditaryInternalDeletionWeightTargets.ActualDecrease := by
 intro body alpha Delta parent child parentRawJob childRawJob raw parameter row count cutoff W V hp hr hc hrow hl hb hv hw hweight
 apply OriginalHereditaryInternalDeletionLookupProof.actualLookup body alpha Delta raw parameter row count cutoff childRawJob (ltF V W) hrow hl hb hv
 intro beta j Theta window gamma typ deleted erased childParameter hj hparam hlength hbound htype hdelete herase hcp hchild
 have hp' := renameInto hp j Theta hj
 have hr' := renameInto hr j Theta hj
 have hc' := renameInto hc j Theta hj
 rw [graph1Rename] at hp' hc'
 rw [graph2Rename] at hr'
 have hparentFields := OriginalHereditaryInternalExpansionFieldsProof.fieldsOfForget
   (parent.relabel j) (parentRawJob.relabel j) (raw.relabel j) (parameter.relabel j) window gamma hp' hr' hparam
 have hchildFields := OriginalHereditaryInternalExpansionFieldsProof.fieldsOfForget
   (child.relabel j) (childRawJob.relabel j) erased childParameter window deleted hc' hchild hcp
 have hw' := renameInto hw j Theta hj
 have hweight' := renameInto hweight j Theta hj
 rw [graph1Rename] at hw' hweight'
 simp only [orderRename]
 exact atCoordinates (parent.relabel j) (child.relabel j) (raw.relabel j) erased gamma deleted typ
   (cutoff.relabel j) (count.relabel j) (W.relabel j) (V.relabel j)
   hparentFields hchildFields herase hlength hbound hdelete hw' hweight'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionWeightProof
