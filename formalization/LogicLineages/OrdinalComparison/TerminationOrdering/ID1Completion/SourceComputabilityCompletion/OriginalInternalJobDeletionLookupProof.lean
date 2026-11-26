module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobContextTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalDeletionLookupProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeel (graph5)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof (symm refl)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalInternalJobAdmissible
open OriginalInternalIndexedPrefixCasesTargets (bump)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open InternalOriginalOrderSyntaxProof (orderRename)
open InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel)
theorem bumpRename {beta : Type} (k : Nat) (x : OTerm alpha) (j : alpha → beta) :
 (bump k x).relabel j = bump k (x.relabel j) := by
 induction k with
 | zero => rfl
 | succ k ih => simp only [bump,sucRelabel,ih]

theorem deletionLookup (H : Program 1) (M W : Program 2) (arity : Nat)
 (index cutoff role typ raw parameter gamma c row count rawCell inheritedAnnotation child childRole childType typed stored annotation childRaw childParameter childGamma : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
 (hindex : Nonempty (Derivation body Delta (eqn index (bump arity cutoff))))
 (hrow : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.deletionJobs row raw parameter)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count row)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell cutoff row)))
 (hinherit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inheritedAnnotation role typ)))
 (hdecor : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (hann : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma)))
 : Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 apply OriginalHereditaryInternalDeletionLookupProof.actualLookup body alpha Delta raw parameter row count cutoff rawCell _ hrow hl hb hlookup
 intro beta j Theta queryC queryGamma erasedType deleted erased erasedParameter hj hqp hlen hbound hkey hdelete herase hparam hcell
 rw [admissibleRename]
 have ha' := renameInto ha j Theta hj
 have hp' := renameInto hp j Theta hj
 have harity' := renameInto harity j Theta hj
 have hindex' := renameInto hindex j Theta hj
 have hinherit' := renameInto hinherit j Theta hj
 have hdecor' := renameInto hdecor j Theta hj
 have hcp' := renameInto hcp j Theta hj
 have ht' := renameInto ht j Theta hj
 have hann' := renameInto hann j Theta hj
 have hcr' := renameInto hcr j Theta hj
 have hcg' := renameInto hcg j Theta hj
 simp only [admissibleRename,graph1Rename,graph2Rename,graph5Rename,eqnRelabel,bumpRename,GuardedSourceSyntaxProof.numeralRename] at ha' hp' harity' hindex' hinherit' hdecor' hcp' ht' hann' hcr' hcg'
 exact OriginalInternalJobDeletionGeometryProof.atGeometry H M W arity
  (index.relabel j) (cutoff.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j)
  (parameter.relabel j) (gamma.relabel j) (c.relabel j) (count.relabel j) queryGamma queryC deleted erasedType erased
  (rawCell.relabel j) erasedParameter (inheritedAnnotation.relabel j) (child.relabel j)
  (childRole.relabel j) (childType.relabel j) (typed.relabel j) (stored.relabel j) (annotation.relabel j)
  (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j)
  ha' hp' hqp harity' hindex' hlen hbound hdelete hkey herase hcell hparam
  hinherit' hdecor' hcp' ht' hann' hcr' hcg'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionLookupProof
