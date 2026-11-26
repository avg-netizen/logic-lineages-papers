module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawExpansionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedScanLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowScanRecoverProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalAdditionLawsProof (add)
open OriginalContextInsertion (lengthGraph)
open OriginalContextInsertionSyntaxProof (lengthRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.decorateAll OriginalHereditaryAnnotatedExpansion.scan
theorem decorateRecover (role typ raw parameter rawJob tagged job jobs full : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tagged typ rawJob)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role tagged)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion full job))) :
    Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll full role typ raw jobs)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
  have hrole := unaryValue InternalUnpair.left (.projection 0) role job xs
    (pairLeft job role tagged hj) (projectionValue 0 xs)
  have htag := unaryValue InternalUnpair.right (.projection 0) tagged job xs
    (pairRight job role tagged hj) (projectionValue 0 xs)
  have htyp := unaryValue InternalUnpair.left (rightOf (.projection 0)) typ tagged xs
    (pairLeft tagged typ rawJob ht) htag
  have hrj := unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob tagged xs
    (pairRight tagged typ rawJob ht) htag
  have hraw := unaryValue InternalUnpair.left OriginalHereditaryAnnotatedExpansion.originalJob raw rawJob xs
    (pairLeft rawJob raw parameter hr) hrj
  have hparam := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedExpansion.originalJob parameter rawJob xs
    (pairRight rawJob raw parameter hr) hrj
  have hexp := binaryValue OriginalHereditaryExpansion.expansion
    (leftOf OriginalHereditaryAnnotatedExpansion.originalJob)
    (rightOf OriginalHereditaryAnnotatedExpansion.originalJob) jobs raw parameter xs he hraw hparam
  apply compositionRecover OriginalHereditaryAnnotatedExpansion.decorateAll _ full xs
    (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) hf
  intro i
  exact Fin.cases hrole (Fin.cases htyp (Fin.cases hraw (Fin.cases hexp (fun k => Fin.elim0 k)))) i
theorem actualLength (job role typ typed rawJob raw parameter gamma c children deletions jobs : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (lengthGraph deletions gamma)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 : Nonempty (Derivation body Delta (lengthGraph (add children deletions) jobs)) := by
 apply programCases OriginalHereditaryExpansion.expansion (Fin.cons raw (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta rawJobs hi hq
 simp only [consTermRename,emptyRename] at hq
 simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have he' := renameInto he j Theta hi
 simp only [graph1Rename,graph2Rename,lengthRename] at hj' ht' hr' hp' ha' hl' he'
 have hrawlen := SourceFramedRawExpansionLengthProof.rawLength
   (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j)
   (children.relabel j) (deletions.relabel j) rawJobs ha' hp' hl' hq
 have hdec := decorateRecover (role.relabel j) (typ.relabel j) (raw.relabel j)
   (parameter.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j) rawJobs (jobs.relabel j)
   hr' ht' hj' hq he'
 have hscan := SixSol20261113.Context.NarrowScanRecoverProof.scanFromAll
   (role.relabel j) (typ.relabel j) (raw.relabel j) rawJobs (jobs.relabel j)
   (add (children.relabel j) (deletions.relabel j)) hdec hrawlen
 exact SourceFramedScanLengthProof.scanLength (add (children.relabel j) (deletions.relabel j))
   (role.relabel j) (typ.relabel j) (raw.relabel j) rawJobs (jobs.relabel j) hscan
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedExpansionLengthProof
