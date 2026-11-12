module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobChildConsumerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalRawExpansionLookupProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobArityRecoverProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobDeletionLookupProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobRawPreservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof (projectionValue)
open OriginalInternalJobAdmissible OriginalInternalJobAdmissibleTransportSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem rawPreservation
 (firstOne : OriginalInternalJobChildCasesTargets.ActualCases true 1)
 (firstTwo : OriginalInternalJobChildCasesTargets.ActualCases true 2)
 (second : OriginalInternalJobChildCasesTargets.ActualCases false 2)
 (H : Program 1) (M W : Program 2)
 (index role typ raw rawCell parameter gamma c child childRole childType typed stored annotation childRaw childParameter childGamma inherited jobs count : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Admissible H M W role typ raw gamma c)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (hexp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs raw parameter)))
 (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count jobs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below index count)))
 (hlookup : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup rawCell index jobs)))
 (hinherit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing inherited role typ)))
 (hd : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.decorate child index role typ raw rawCell)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child childRole typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed childType stored)))
 (hann : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing annotation childRole childType)))
 (hcr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing stored childRaw childParameter)))
 (hcg : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter c childGamma))) :
 Nonempty (Derivation body Delta (Admissible H M W childRole childType childRaw childGamma c)) := by
 apply OriginalInternalRawExpansionLookupProof.actualCases body alpha Delta raw parameter jobs count index rawCell _ hexp hl hb hlookup
 · intro beta j Theta arity haCases hj harity hi hcell
   rw [admissibleRename]
   have ha' := renameInto ha j Theta hj
   have hp' := renameInto hp j Theta hj
   have hinherit' := renameInto hinherit j Theta hj
   have hd' := renameInto hd j Theta hj
   have hcp' := renameInto hcp j Theta hj
   have ht' := renameInto ht j Theta hj
   have hann' := renameInto hann j Theta hj
   have hcr' := renameInto hcr j Theta hj
   have hcg' := renameInto hcg j Theta hj
   simp only [admissibleRename,graph2Rename,graph5Rename] at ha' hp' hinherit' hd' hcp' ht' hann' hcr' hcg'
   let xs : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
   have hu := OriginalInternalJobArityRecoverProof.arityRecoverAt (.projection 0) (numeral arity) (raw.relabel j) xs (projectionValue 0 xs) harity
   rcases haCases with rfl | rfl
   · exact OriginalInternalJobChildConsumerProof.fromCases true 1 firstOne H M W
      (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (rawCell.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) (child.relabel j) (childRole.relabel j) (childType.relabel j) (typed.relabel j) (stored.relabel j) (annotation.relabel j) (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j)
      hi ha' hp' hu hcell hd' hcp' ht' hann' hcr' hcg'
   · exact OriginalInternalJobChildConsumerProof.fromCases true 2 firstTwo H M W
      (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (rawCell.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) (child.relabel j) (childRole.relabel j) (childType.relabel j) (typed.relabel j) (stored.relabel j) (annotation.relabel j) (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j)
      hi ha' hp' hu hcell hd' hcp' ht' hann' hcr' hcg'
 · intro beta j Theta hj harity hi hcell
   rw [admissibleRename]
   have ha' := renameInto ha j Theta hj
   have hp' := renameInto hp j Theta hj
   have hinherit' := renameInto hinherit j Theta hj
   have hd' := renameInto hd j Theta hj
   have hcp' := renameInto hcp j Theta hj
   have ht' := renameInto ht j Theta hj
   have hann' := renameInto hann j Theta hj
   have hcr' := renameInto hcr j Theta hj
   have hcg' := renameInto hcg j Theta hj
   simp only [admissibleRename,graph2Rename,graph5Rename] at ha' hp' hinherit' hd' hcp' ht' hann' hcr' hcg'
   let xs : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
   have hu := OriginalInternalJobArityRecoverProof.arityRecoverAt (.projection 0) (numeral 2) (raw.relabel j) xs (projectionValue 0 xs) harity
   exact OriginalInternalJobChildConsumerProof.fromCases false 2 second H M W
      (index.relabel j) (role.relabel j) (typ.relabel j) (raw.relabel j) (rawCell.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) (child.relabel j) (childRole.relabel j) (childType.relabel j) (typed.relabel j) (stored.relabel j) (annotation.relabel j) (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j)
      hi ha' hp' hu hcell hd' hcp' ht' hann' hcr' hcg'
 · intro beta j Theta arity row cutoff rowCount _haCases hj harity hi hrow hlen hbound hlook
   rw [admissibleRename]
   have ha' := renameInto ha j Theta hj
   have hp' := renameInto hp j Theta hj
   have hinherit' := renameInto hinherit j Theta hj
   have hd' := renameInto hd j Theta hj
   have hcp' := renameInto hcp j Theta hj
   have ht' := renameInto ht j Theta hj
   have hann' := renameInto hann j Theta hj
   have hcr' := renameInto hcr j Theta hj
   have hcg' := renameInto hcg j Theta hj
   simp only [admissibleRename,graph2Rename,graph5Rename] at ha' hp' hinherit' hd' hcp' ht' hann' hcr' hcg'
   let xs : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
   have hu := OriginalInternalJobArityRecoverProof.arityRecoverAt (.projection 0) (numeral arity) (raw.relabel j) xs (projectionValue 0 xs) harity
   exact OriginalInternalJobDeletionLookupProof.deletionLookup H M W arity
    (index.relabel j) cutoff (role.relabel j) (typ.relabel j) (raw.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) row rowCount (rawCell.relabel j) (inherited.relabel j) (child.relabel j) (childRole.relabel j) (childType.relabel j) (typed.relabel j) (stored.relabel j) (annotation.relabel j) (childRaw.relabel j) (childParameter.relabel j) (childGamma.relabel j)
    ha' hp' hu hi hrow (by simpa only [OriginalContextInsertion.lengthGraph,graph1] using hlen) hbound hlook hinherit' hd' hcp' ht' hann' hcr' hcg'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobRawPreservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobRawPreservationProof
