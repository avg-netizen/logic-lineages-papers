module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.AnnotationSuffixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.InheritedMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename andIntro)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InternalTagArithmeticSupportProof (addZero)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion (lengthGraph)
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalInternalIndexedPrefixCasesTargets (bump)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261112.Context
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph OriginalHereditaryAnnotatedExpansion.scan
  OriginalHereditaryAnnotatedExpansion.decorateAll InternalListMap.map

theorem bumpZero (arity : Nat) : bump arity (z : OTerm alpha) = numeral arity := by
  induction arity with
  | zero => rfl
  | succ arity ih => change suc (bump arity z) = suc (numeral arity); rw [ih]

theorem childLength (arity : Nat) (raw parameter front : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter))) :
    Nonempty (Derivation body Delta (lengthGraph (numeral arity) front)) := by
  have h := SixSol20261112.Runtime.ScheduleCountRowsProof.rowsExact raw parameter front z front
    (numeral arity) z hc (AppendIdentityProof.actualRightZero body alpha Delta front) ha
    OriginalContextInsertionLengthProof.lengthZero
  exact outputTransport OriginalContextInsertion.length (add (numeral arity) z) (numeral arity)
    (Fin.cons front Fin.elim0) ⟨addZero (numeral arity)⟩ h

theorem rawExpansion (raw parameter front suffix jobs : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
    (hd : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs suffix raw parameter)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix))) :
    Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)) :=
  binaryValue InternalApplicationValidityStackAppend.append
    OriginalHereditaryExpansion.childJobs OriginalHereditaryExpansion.deletionJobs
    jobs front suffix (Fin.cons raw (Fin.cons parameter Fin.elim0)) hj hc hd

theorem decorateRecover (typ raw parameter rawJob tagged job jobs full : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tagged typ rawJob)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z tagged)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
    (hf : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion full job))) :
    Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll full z typ raw jobs)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
  have hrole := unaryValue InternalUnpair.left (.projection 0) z job xs
    (pairLeft job z tagged hj) (projectionValue 0 xs)
  have htag := unaryValue InternalUnpair.right (.projection 0) tagged job xs
    (pairRight job z tagged hj) (projectionValue 0 xs)
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
    (Fin.cons z (Fin.cons typ (Fin.cons raw (Fin.cons jobs Fin.elim0)))) hf
  intro i
  exact Fin.cases hrole (Fin.cases htyp (Fin.cases hraw (Fin.cases hexp (fun k => Fin.elim0 k)))) i

theorem splitAtLength (arity : Nat) (typ raw parameter front suffix jobs annotatedFront count mapped full : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
    (hc : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.childJobs front raw parameter)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append jobs front suffix)))
    (hp : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedFront (numeral arity) z typ raw jobs)))
    (hl : Nonempty (Derivation body Delta (lengthGraph count suffix)))
    (hm : Nonempty (Derivation body Delta (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) mapped suffix typ)))
    (hf : Nonempty (Derivation body Delta (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll full z typ raw jobs))) :
    Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append full annotatedFront mapped)) := by
  have hfront := childLength arity raw parameter front ha hc
  have hlength := SixSol20261112.Runtime.ScheduleCountRowsProof.rowsExact raw parameter front suffix jobs
    (numeral arity) count hc hj ha hl
  have hscan := OriginalHereditaryInternalAnnotatedScanProof.scanFromAll z typ raw jobs full
    (add (numeral arity) count) hf hlength
  apply AnnotationSuffixProof.actualInheritedScanSplit arity body alpha Delta z typ raw front suffix jobs
    annotatedFront count full mapped ha
  · simpa only [bumpZero] using hfront
  · exact hj
  · simpa only [bumpZero] using hp
  · exact hl
  · simpa only [bumpZero] using hscan
  · exact hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ExpansionSupportProof
