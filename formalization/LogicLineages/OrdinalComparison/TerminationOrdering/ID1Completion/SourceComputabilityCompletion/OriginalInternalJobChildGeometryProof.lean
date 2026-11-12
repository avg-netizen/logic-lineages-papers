module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildTreeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawSameContextProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
theorem actualGeometry : OriginalInternalJobChildGeometryTargets.ActualGeometry := by
 intro body alpha Delta parent role typ typed rawJob raw parameter c gamma row count index child psi hp ht hr hparam he hl hb hlook next
 apply OriginalInternalJobRawCellCasesProof.rawCellCases parent role typ typed rawJob raw parameter row count index child psi hp ht hr he hl hb hlook
 intro beta j Theta jobs rawCell hinc hexp hlen hbound hlookup hdecor
 have hparam' := renameInto hparam j Theta hinc
 rw [graph2Rename] at hparam'
 apply OriginalInternalRawSameContextProof.actualCases body beta Theta
  (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) jobs (count.relabel j) (index.relabel j) rawCell (psi.relabel j)
  hparam' hexp hlen hbound hlookup
 intro gammaType k Xi childRaw childParameter childGamma hk hraw hcg
 have hdecor' := renameInto hdecor k Xi hk
 rw [graph5Rename] at hdecor'
 apply OriginalInternalJobChildTreeProof.treeCases ((child.relabel j).relabel k) ((psi.relabel j).relabel k)
 intro epsilon l Omega childRole childType childTyped childRawJob hli hcp hct
 have hraw' := renameInto hraw l Omega hli
 have hcg' := renameInto hcg l Omega hli
 have hdecor2 := renameInto hdecor' l Omega hli
 rw [graph2Rename] at hraw' hcg'
 rw [graph5Rename] at hdecor2
 have hforget := OriginalHereditaryInternalExpansionDecorationProof.decorateForget
  (((index.relabel j).relabel k).relabel l) (((role.relabel j).relabel k).relabel l)
  (((typ.relabel j).relabel k).relabel l) (((raw.relabel j).relabel k).relabel l)
  ((rawCell.relabel k).relabel l) (((child.relabel j).relabel k).relabel l) hdecor2
 have hstored := OriginalInternalDecorationStoredProof.forgetOfPairs (((child.relabel j).relabel k).relabel l)
  childRole childTyped childType childRawJob hcp hct
 have heq := valueUnique OriginalHereditaryAnnotatedExpansion.forget ((rawCell.relabel k).relabel l) childRawJob
  (Fin.cons (((child.relabel j).relabel k).relabel l) Fin.elim0) hforget hstored
 have hcr := outputTransport InternalPairing.pairing ((rawCell.relabel k).relabel l) childRawJob
  (Fin.cons (childRaw.relabel l) (Fin.cons (childParameter.relabel l) Fin.elim0)) heq hraw'
 have incl : ∀ f ∈ Delta, f.relabel (l ∘ k ∘ j) ∈ Omega := by
  intro f hf
  simpa only [← formulaRelabelComposition,Function.comp_assoc] using hli _ (hk _ (hinc f hf))
 have result := next epsilon (l ∘ k ∘ j) Omega childRole childType childTyped childRawJob
  (childRaw.relabel l) (childParameter.relabel l) (childGamma.relabel l) incl
  (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hcp) hct hcr
  (by simpa only [Term.relabel_relabel,Function.comp_assoc] using hcg')
 simpa only [formulaRelabelComposition,Function.comp_assoc] using result
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildGeometryProof
