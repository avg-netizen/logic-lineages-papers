module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAnnotationsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobRawCellCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleLookupTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobLookupAssemblyProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
/-- Staging theorem with explicit independently provable constructor cases;
the public ActualLookup endpoint must instantiate all three suppliers. -/
theorem fromConstructors
 (firstOne : OriginalInternalJobChildCasesTargets.ActualCases true 1)
 (firstTwo : OriginalInternalJobChildCasesTargets.ActualCases true 2)
 (second : OriginalInternalJobChildCasesTargets.ActualCases false 2) :
 OriginalInternalJobAdmissibleLookupTargets.ActualLookup := by
 intro body H M W alpha Delta parent role typ typed rawJob raw parameter gamma c
   child childRole childType childTyped childRawJob childRaw childParameter childGamma row count index
   hp ht hr hparam hcp hct hcr hcg ha he hl hb hlook
 apply OriginalInternalJobRawCellCasesProof.rawCellCases parent role typ typed rawJob raw parameter row count index child _ hp ht hr he hl hb hlook
 intro beta j Theta jobs cell hj hexp hlen hbound hlookup hdecor
 rw [admissibleRename]
 have hparam' := renameInto hparam j Theta hj
 have hcp' := renameInto hcp j Theta hj
 have hct' := renameInto hct j Theta hj
 have hcr' := renameInto hcr j Theta hj
 have hcg' := renameInto hcg j Theta hj
 have ha' := renameInto ha j Theta hj
 simp only [graph2Rename,admissibleRename] at hparam' hcp' hct' hcr' hcg' ha'
 exact OriginalInternalJobAnnotationsProof.withoutAnnotations firstOne firstTwo second H M W
  (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) cell (parameter.relabel j) (gamma.relabel j) (c.relabel j) (child.relabel j) (childRole.relabel j) (childType.relabel j) (childTyped.relabel j) (childRawJob.relabel j) (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j) jobs (count.relabel j)
  ha' hparam' hexp hlen hbound hlookup hdecor hcp' hct' hcr' hcg'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobLookupAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobLookupAssemblyProof
