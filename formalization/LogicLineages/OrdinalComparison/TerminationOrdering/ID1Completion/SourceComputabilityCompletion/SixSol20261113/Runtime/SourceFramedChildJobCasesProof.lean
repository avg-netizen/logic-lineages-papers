module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildAdmissibilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildDecreaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof OriginalHereditaryInternalAgendaBindingProof
open OriginalHereditaryInternalJobRow OriginalHereditaryInternalJobRowSyntaxProof OriginalHereditaryInternalJobRowBindingProof
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open SixSol20261113.Runtime.SourceFramedChildJobProof
theorem childWithGeometry (H : Program 1) (M W : Program 2) (c B parent role typ typed rawJob raw parameter gamma weight row count index child childRole childType childTyped childRawJob childRaw childParameter childGamma : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (jobFields H M W c B parent role typ typed rawJob raw parameter gamma weight)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole childTyped)))
 (hct : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childTyped childType childRawJob)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childRawJob childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)))
 : Nonempty (Derivation body Delta (Job H M W c B child)) := by
 apply InternalAcceptanceSupportProof.programCases OriginalHereditaryFuelProgram.weight (Fin.cons child Fin.elim0) _
 intro beta j Theta childWeight hinc hw
 simp only [consTermRename,emptyRename] at hw
 rw [jobRename]
 have hf' := renameInto hf j Theta hinc
 have he' := renameInto he j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hk' := renameInto hk j Theta hinc
 have hcp' := renameInto hcp j Theta hinc
 have hct' := renameInto hct j Theta hinc
 have hcr' := renameInto hcr j Theta hinc
 have hcg' := renameInto hcg j Theta hinc
 simp only [jobFieldsRename,graph1Rename,graph2Rename,OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at hf' he' hl' hb' hk' hcp' hct' hcr' hcg'
 exact childAtFields H M W (c.relabel j) (B.relabel j) (parent.relabel j) (role.relabel j) (typ.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (gamma.relabel j) (weight.relabel j) (row.relabel j) (count.relabel j) (index.relabel j) (child.relabel j)
  (childRole.relabel j) (childType.relabel j) (childTyped.relabel j) (childRawJob.relabel j) (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j) childWeight hf' he' hl' hb' hk' hcp' hct' hcr' hcg' hw
theorem childFields (H : Program 1) (M W : Program 2) (c B parent role typ typed rawJob raw parameter gamma weight row count index child : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (jobFields H M W c B parent role typ typed rawJob raw parameter gamma weight)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row)))
 : Nonempty (Derivation body Delta (Job H M W c B child)) := by
 apply SixSol20261113.Runtime.SourceFramedChildGeometryProof.actualGeometry body alpha Delta
  parent role typ typed rawJob raw parameter c gamma row count index child _
  (andLeft hf) (andLeft (andRight hf)) (andLeft (andRight (andRight hf)))
  (andLeft (andRight (andRight (andRight hf)))) he hl hb hk
 intro beta j Theta childRole childType childTyped childRawJob childRaw childParameter childGamma hinc hcp hct hcr hcg
 rw [jobRename]
 have hf' := renameInto hf j Theta hinc
 have he' := renameInto he j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hk' := renameInto hk j Theta hinc
 simp only [jobFieldsRename,graph1Rename,graph2Rename,OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at hf' he' hl' hb' hk'
 exact childWithGeometry H M W (c.relabel j) (B.relabel j) (parent.relabel j) (role.relabel j) (typ.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (gamma.relabel j) (weight.relabel j) (row.relabel j) (count.relabel j) (index.relabel j) (child.relabel j)
  childRole childType childTyped childRawJob childRaw childParameter childGamma hf' he' hl' hb' hk' hcp hct hcr hcg
theorem childAt (H : Program 1) (M W : Program 2) (c B parent row count index child : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (Job H M W c B parent)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup child index row))) :
 Nonempty (Derivation body Delta (Job H M W c B child)) := by
 apply jobCases H M W c B parent _ hp
 intro beta j Theta role typ typed rawJob raw parameter gamma weight hinc hf
 rw [jobRename]
 have he' := renameInto he j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hb' := renameInto hb j Theta hinc
 have hk' := renameInto hk j Theta hinc
 simp only [jobFieldsRename,graph1Rename,graph2Rename,OriginalContextInsertion.Below,InternalOriginalOrderSyntaxProof.orderRename] at he' hl' hb' hk'
 exact childFields H M W (c.relabel j) (B.relabel j) (parent.relabel j)
  role typ typed rawJob raw parameter gamma weight (row.relabel j) (count.relabel j) (index.relabel j) (child.relabel j) hf he' hl' hb' hk'

theorem actualExpansion : OriginalHereditaryInternalJobExpansionTargets.Expansion := by
 intro body alpha Delta H M W c B parent row hp he
 apply jobsIntro H M W c B row
 intro beta j Theta count index child hinc hfields
 have hp' := renameInto hp j Theta hinc
 have he' := renameInto he j Theta hinc
 rw [jobRename] at hp'
 rw [graph1Rename] at he'
 exact childAt H M W (c.relabel j) (B.relabel j) (parent.relabel j) (row.relabel j) count index child hp' he'
  (andLeft hfields) (andLeft (andRight hfields)) (andRight (andRight hfields))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedChildJobCasesProof
