module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildCasesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobPacketReconcileProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsumerProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Proof-side adapter; the explicit constructor-case supplier is instantiated
only after its independently frozen endpoint has been established. -/
theorem fromCases (first : Bool) (arity : Nat)
 (supply : OriginalInternalJobChildCasesTargets.ActualCases first arity)
 (H : Program 1) (M W : Program 2)
 (index role typ raw rawCell parameter gamma c child childRole childType typed stored annotation childRaw childParameter childGamma : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (eqn index (numeral (if first then 0 else 1)))))
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (harity : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) (numeral arity) raw)))
 (hcell : Nonempty (Derivation body Delta (graph2 (if first then OriginalHereditaryExpansion.firstJob else OriginalHereditaryExpansion.secondJob) rawCell raw parameter)))
 (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (hann : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma))) :
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 apply supply body alpha Delta H M W role typ raw rawCell parameter c gamma _ ha hp harity hcell
 intro beta j Theta outRole outType outRaw outGamma outParam outAnnotation hj hpacket
 rw [admissibleRename]
 have hi' := renameInto hi j Theta hj
 have hd' := renameInto hd j Theta hj
 have hcp' := renameInto hcp j Theta hj
 have ht' := renameInto ht j Theta hj
 have hann' := renameInto hann j Theta hj
 have hcr' := renameInto hcr j Theta hj
 have hcg' := renameInto hcg j Theta hj
 simp only [eqnRelabel,numeralRename,graph2Rename,graph5Rename] at hi' hd' hcp' ht' hann' hcr' hcg'
 have hpacket' := hpacket
 simp only [numeralRename] at hpacket'
 exact OriginalInternalJobPacketReconcileProof.reconcilePacket H M W
  (index.relabel j) (numeral (if first then 0 else 1)) (role.relabel j) (typ.relabel j) (raw.relabel j) (rawCell.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) (child.relabel j) (childRole.relabel j) (childType.relabel j) (typed.relabel j) (stored.relabel j) (annotation.relabel j)
  outRole outType outRaw outGamma outParam outAnnotation (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j)
  hi' hpacket' hd' hcp' ht' hann' hcr' hcg'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsumerProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsumerProof
