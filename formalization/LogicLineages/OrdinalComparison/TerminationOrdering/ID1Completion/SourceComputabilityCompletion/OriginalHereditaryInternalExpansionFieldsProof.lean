module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro)
open OriginalHereditaryInternalWeightDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Literal annotation pairs do not alter the raw/context coordinates used by
weight. No restriction on the role, type, raw code, or window is assumed. -/
theorem fieldsOfPairs (job role tagged typ rawJob raw parameter window gamma : OTerm alpha)
 (hjob : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role tagged)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tagged typ rawJob)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma))) :
 Nonempty (Derivation body Delta (fields job raw gamma)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have htagged : Nonempty (Derivation body Delta (programGraph (rightOf (.projection 0)) tagged xs)) :=
   unaryValue InternalUnpair.right (.projection 0) tagged job xs
     (pairRight job role tagged hjob) (projectionValue 0 xs)
 have hrawJob : Nonempty (Derivation body Delta (programGraph OriginalHereditaryFuelProgram.rawJob rawJob xs)) :=
   unaryValue InternalUnpair.right (rightOf (.projection 0)) rawJob tagged xs
     (pairRight tagged typ rawJob htag) htagged
 have hfirst : Nonempty (Derivation body Delta (graph1 rawSelector raw job)) :=
   unaryValue InternalUnpair.left OriginalHereditaryFuelProgram.rawJob raw rawJob xs
     (pairLeft rawJob raw parameter hraw) hrawJob
 have hparameter : Nonempty (Derivation body Delta
   (programGraph (rightOf OriginalHereditaryFuelProgram.rawJob) parameter xs)) :=
   unaryValue InternalUnpair.right OriginalHereditaryFuelProgram.rawJob parameter rawJob xs
     (pairRight rawJob raw parameter hraw) hrawJob
 have hcontext : Nonempty (Derivation body Delta (graph1 contextSelector gamma job)) :=
   unaryValue InternalUnpair.right (rightOf OriginalHereditaryFuelProgram.rawJob) gamma parameter xs
     (pairRight parameter window gamma hparam) hparameter
 exact andIntro hfirst hcontext

/-- Once the copied raw job is exposed by annotated-scan inversion, its pair
fields determine exactly the two weight inputs, independent of annotations. -/
theorem fieldsOfForget (job rawJob raw parameter window gamma : OTerm alpha)
 (hforget : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.forget rawJob job)))
 (hraw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hparam : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma))) :
 Nonempty (Derivation body Delta (fields job raw gamma)) := by
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 have hfirst : Nonempty (Derivation body Delta (graph1 rawSelector raw job)) :=
   unaryValue InternalUnpair.left OriginalHereditaryFuelProgram.rawJob raw rawJob xs
     (pairLeft rawJob raw parameter hraw) hforget
 have hparameter : Nonempty (Derivation body Delta
   (programGraph (rightOf OriginalHereditaryFuelProgram.rawJob) parameter xs)) :=
   unaryValue InternalUnpair.right OriginalHereditaryFuelProgram.rawJob parameter rawJob xs
     (pairRight rawJob raw parameter hraw) hforget
 have hcontext : Nonempty (Derivation body Delta (graph1 contextSelector gamma job)) :=
   unaryValue InternalUnpair.right (rightOf OriginalHereditaryFuelProgram.rawJob) gamma parameter xs
     (pairRight parameter window gamma hparam) hparameter
 exact andIntro hfirst hcontext

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionFieldsProof
