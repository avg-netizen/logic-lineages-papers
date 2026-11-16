module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.GuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalVariableSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.OutputProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceBranchProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem successValue (n : Nat) (arity : Fin n → Nat) (raw result args packed : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph1 Continuation20261114.OriginalHeadResult.headResult result raw)))
    (ha : Nonempty (Derivation body Delta (graph1 (arguments n arity) args raw)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed result args)))
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) (suc z) raw))) :
    Nonempty (Derivation body Delta (graph1 (signature n arity) (suc packed) raw)) := by
  have hpair := binaryValue InternalPairing.pairing Continuation20261114.OriginalHeadResult.headResult (arguments n arity)
    packed result args ![raw] hp hr ha
  have hout := unaryValue .succ (pairOf Continuation20261114.OriginalHeadResult.headResult (arguments n arity))
    (suc packed) packed ![raw] (successorValue (Fin.cons packed Fin.elim0)) hpair
  exact successorBranchIntro _ _ _ (suc packed) z ![raw] hg hout

theorem failureValue (n : Nat) (arity : Fin n → Nat) (raw : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (Continuation20261115.OriginalHeadDecoderValidity.check n) z raw))) :
    Nonempty (Derivation body Delta (graph1 (signature n arity) z raw)) :=
  zeroBranchIntro _ _ _ z ![raw] hg (constantValue 0 ![raw])

theorem successorProgramNonzero (p : Program 1) (raw out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph1 (succOf p) out raw))) :
    Nonempty (Derivation body Delta (eqn out z).not) := by
  apply programCases p ![raw] _
  intro beta j Theta value hj hp
  have hx : (fun i => (![raw] i).relabel j) = ![raw.relabel j] := by
    funext i; fin_cases i; rfl
  rw [hx] at hp
  change Nonempty (Derivation body Theta (((eqn out z).relabel j).not))
  rw [eqnRelabel,zRelabel]
  have hoj := renameInto ho j Theta hj
  rw [graph1Rename] at hoj
  have hv := unaryValue .succ p (suc value) value ![raw.relabel j]
    (successorValue (Fin.cons value Fin.elim0)) hp
  obtain ⟨he⟩ := valueUnique (succOf p) (out.relabel j) (suc value) ![raw.relabel j] hoj hv
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply
    (trans (symm (InternalBetaTotalityProof.addHyp he _)) (Derivation.hypothesis List.mem_cons_self)))⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.OutputProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalConcreteHeadSignature.OutputProof
