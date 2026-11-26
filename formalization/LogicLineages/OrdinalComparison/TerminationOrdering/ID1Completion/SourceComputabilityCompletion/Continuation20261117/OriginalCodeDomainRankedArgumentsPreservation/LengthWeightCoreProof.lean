module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightQueriesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel)
open InternalTagArithmeticSupportProof (refl symm)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LengthWeight LengthWeightSyntaxProof LengthWeightBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem nil (count out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count z)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out count z))) :
    Nonempty (Derivation body Delta (result z out)) := by
  have he := OriginalContextInsertionLengthProof.lengthNilRecover count hl
  have hp0 := headTransport InternalPairing.pairing out count z ![z] he hp
  obtain ⟨he0⟩ := valueUnique InternalPairing.pairing out z ![z,z] hp0
    InternalApplicationValidityStackAppendTransitionProof.pairZero
  exact outputTransport (Auxiliary.Fold.weighted weight) z out ![z] ⟨symm he0⟩
    (Auxiliary.FoldValueProof.nil weight)

theorem nonzero (raw count out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out count z)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw)))
    (hn : Nonempty (Derivation body Delta (eqn raw z).not)) :
    Nonempty (Derivation body Delta (result raw out)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases LengthWeightQueriesProof.queries ![raw] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![raw] i).relabel j) = ![raw.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [resultRename]
  have hlj := renameInto hl j Theta hj
  rw [graph1Rename] at hlj
  have hpj := renameInto hp j Theta hj
  simp only [graph2Rename,zRelabel] at hpj
  have ihj := renameInto ih j Theta hj
  rw [belowRawRename] at ihj
  have hnj := renameInto hn j Theta hj
  simp only [OriginalTypedDecoderTransportLogicalProof.notRename,eqnRelabel,zRelabel] at hnj
  obtain ⟨hc,ht,ha,hw⟩ := LengthWeightQueriesProof.recover (raw.relabel j) ys hnj hq
  have he := OriginalContextInsertionLengthProof.lengthConsRecover (raw.relabel j) (ys 0)
    (ys 1) (count.relabel j) (ys 2) hc hlj ht
  have hp' := headTransport InternalPairing.pairing (out.relabel j) (count.relabel j)
    (suc (ys 2)) ![z] he hpj
  have hs := InternalListCodecDecompositionSupportProof.consTailDescent (raw.relabel j) (ys 0) (ys 1) hc
  have hf := belowRawApply (raw.relabel j) (ys 1) (ys 2) (ys 3) ihj hs (andIntro ht ha)
  exact LengthWeightValueProof.consValue (raw.relabel j) (ys 0) (ys 1) (ys 2) (ys 3)
    (ys 4) (out.relabel j) hc hf ha hw hp'

theorem atRaw (raw count out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing out count z)))
    (ih : Nonempty (Derivation body Delta (BelowRaw raw))) :
    Nonempty (Derivation body Delta (result raw out)) := by
  apply formulaCases (eqn raw z)
  · have he : Nonempty (Derivation body (eqn raw z :: Delta) (eqn raw z)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hl0 := headTransport OriginalContextInsertion.length count raw z Fin.elim0 he (withHyp hl _)
    have hf := nil count out hl0 (withHyp hp _)
    obtain ⟨he⟩ := he
    exact headTransport (Auxiliary.Fold.weighted weight) out z raw Fin.elim0 ⟨symm he⟩ hf
  · exact nonzero raw count out (withHyp hl _) (withHyp hp _) (withHyp ih _)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.LengthWeightCoreProof
