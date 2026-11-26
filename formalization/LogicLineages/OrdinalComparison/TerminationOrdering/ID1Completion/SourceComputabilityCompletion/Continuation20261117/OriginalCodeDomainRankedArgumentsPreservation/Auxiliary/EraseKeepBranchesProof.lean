module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseBranchAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseResultRenameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseConstructQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepBranchesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel sucRelabel zRelabel)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open EraseInvariant EraseInvariantSyntaxProof EraseResultRenameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem absent (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (z) rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle).not))
    (hf : Nonempty (Derivation body Delta (countEffect tail needle rest (z))))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit remaining)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases EraseConstructQueriesProof.queries ![z,head,rest] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![z,head,rest] i).relabel j) = ![z,head.relabel j,rest.relabel j] := by
    funext i
    fin_cases i
    · change (z : OTerm alpha).relabel j = z
      exact zRelabel j
    · rfl
    · rfl
  rw [hx] at hq
  obtain ⟨hk,ho⟩ := EraseConstructQueriesProof.recover (z) (head.relabel j) (rest.relabel j) ys hq
  rw [resultRename]
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hfj := renameInto hf j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hcj htj hpj haj hapj
  simp only [countEffectRename,zRelabel,sucRelabel] at hfj
  have hej := renameInto he j Theta hj
  simp only [notRename,eqnRelabel] at hej
  obtain ⟨hv,hr⟩ := EraseBranchAtProof.absent (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (acc.relabel j) (rest.relabel j) (ys 0) (ys 1) hcj htj hpj hej hfj hk ho
  exact EraseOutputProof.transfer (list.relabel j) (needle.relabel j) (ys 1) (z) (ys 0)
    (actual.relabel j) (bit.relabel j) (remaining.relabel j) hv ho haj hapj hr

theorem found (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc (suc z) rest)))
    (hf : Nonempty (Derivation body Delta (countEffect tail needle rest (suc z))))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit remaining)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases EraseConstructQueriesProof.queries ![suc z,head,rest] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![suc z,head,rest] i).relabel j) = ![suc z,head.relabel j,rest.relabel j] := by
    funext i
    fin_cases i
    · change (suc (z : OTerm alpha)).relabel j = suc z
      simp only [sucRelabel,zRelabel]
    · rfl
    · rfl
  rw [hx] at hq
  obtain ⟨hk,ho⟩ := EraseConstructQueriesProof.recover (suc z) (head.relabel j) (rest.relabel j) ys hq
  rw [resultRename]
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hfj := renameInto hf j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hcj htj hpj haj hapj
  simp only [countEffectRename,zRelabel,sucRelabel] at hfj
  obtain ⟨hv,hr⟩ := EraseBranchAtProof.found (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (acc.relabel j) (rest.relabel j) (ys 0) (ys 1) hcj htj hpj hfj hk ho
  exact EraseOutputProof.transfer (list.relabel j) (needle.relabel j) (ys 1) (suc z) (ys 0)
    (actual.relabel j) (bit.relabel j) (remaining.relabel j) hv ho haj hapj hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.Auxiliary.EraseKeepBranchesProof
