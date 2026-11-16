module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseChildQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseConsAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseRawTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open OriginalTypedDecoderTransportLogicalProof (notRename)
open EraseInvariant EraseInvariantSyntaxProof EraseInvariantBindingProof EraseResultRenameProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nonzero (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not)) :
    Nonempty (Derivation body Delta (result raw needle bit rest)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases EraseChildQueriesProof.queries ![raw,needle] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw,needle] i).relabel j) = ![raw.relabel j,needle.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [resultRename]
  have hvj := renameInto hv j Theta hj
  have hpj := renameInto hp j Theta hj
  have ihj := renameInto ih j Theta hj
  have hnj := renameInto hn j Theta hj
  rw [graph2Rename] at hvj hpj
  rw [belowRawRename] at ihj
  simp only [notRename,eqnRelabel,zRelabel] at hnj
  obtain ⟨hc,ht,hpair⟩ := EraseChildQueriesProof.recover (raw.relabel j) (needle.relabel j) ys hnj hq
  have hsmall := InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (ys 0) (ys 1) hc
  have htail := belowRawApply (raw.relabel j) (ys 1) (needle.relabel j) (ys 2) (ys 3) (ys 4)
    ihj hsmall (andIntro ht hpair)
  exact EraseConsAtProof.atTail (raw.relabel j) (ys 0) (ys 1) (needle.relabel j) (ys 2) (ys 3) (ys 4)
    (acc.relabel j) (bit.relabel j) (rest.relabel j) hc ht hpair htail hvj hpj

theorem atRaw (raw needle acc bit rest : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph2 Erase.state acc raw needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (result raw needle bit rest)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body ((eqn raw z) :: Delta) (eqn raw z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv0 := headTransport Erase.state acc raw z (Fin.cons needle Fin.elim0) he (withHyp hv _)
    have hnil := EraseNilProof.nil needle acc bit rest hv0 (withHyp hp _)
    obtain ⟨he⟩ := he
    exact EraseRawTransportProof.rawTransport z raw needle bit rest ⟨symm he⟩ hnil
  · exact nonzero raw needle acc bit rest (withHyp hv _) (withHyp hp _) (withHyp ih _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseCoreProof
