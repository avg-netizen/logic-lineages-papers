module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleLookupTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAnnotatedScanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionParentProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobExpansionCoordinatesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem decorateAllFromCoordinates
 (parent role typ typed rawJob raw parameter rawJobs row : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parent role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hj : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion row parent))) :
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll row role typ raw rawJobs)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons parent Fin.elim0
 have hrole := unaryValue InternalUnpair.left (.projection 0) role parent xs (pairLeft parent role typed hp) (projectionValue 0 xs)
 have htyped := unaryValue InternalUnpair.right (.projection 0) typed parent xs (pairRight parent role typed hp) (projectionValue 0 xs)
 have htyp := unaryValue InternalUnpair.left (rightOf (.projection 0)) typ typed xs (pairLeft typed typ rawJob ht) htyped
 have hrawJob : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.originalJob rawJob parent)) :=
  unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob typed xs (pairRight typed typ rawJob ht) htyped
 have hraw := unaryValue InternalUnpair.left OriginalHereditaryAnnotatedExpansion.originalJob raw rawJob xs (pairLeft rawJob raw parameter hr) hrawJob
 have hparameter := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedExpansion.originalJob parameter rawJob xs (pairRight rawJob raw parameter hr) hrawJob
 have hrows := binaryValue OriginalHereditaryExpansion.expansion
  (leftOf OriginalHereditaryAnnotatedExpansion.originalJob) (rightOf OriginalHereditaryAnnotatedExpansion.originalJob)
  rawJobs raw parameter xs hj hraw hparameter
 apply compositionRecover OriginalHereditaryAnnotatedExpansion.decorateAll
  ![leftOf (.projection 0),leftOf (rightOf (.projection 0)),leftOf OriginalHereditaryAnnotatedExpansion.originalJob,
    .composition OriginalHereditaryExpansion.expansion ![leftOf OriginalHereditaryAnnotatedExpansion.originalJob,rightOf OriginalHereditaryAnnotatedExpansion.originalJob] ]
  row xs (Fin.cons role (Fin.cons typ (Fin.cons raw (Fin.cons rawJobs Fin.elim0)))) he
 intro i
 exact Fin.cases hrole (Fin.cases htyp (Fin.cases hraw (Fin.cases hrows (fun k => Fin.elim0 k)))) i
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobExpansionCoordinatesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobExpansionCoordinatesProof
