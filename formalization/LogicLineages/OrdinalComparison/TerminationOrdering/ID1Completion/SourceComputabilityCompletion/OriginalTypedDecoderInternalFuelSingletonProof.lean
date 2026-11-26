module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalTypedDecoderInternalFuelSingletonSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tripleRename {beta : Type} (typ raw gamma : OTerm alpha) (j : alpha → beta) :
    (fun i : Fin 3 => (![typ,raw,gamma] i).relabel j) =
      ![typ.relabel j,raw.relabel j,gamma.relabel j] := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i

theorem singletonAt (H : Program 1) (mode : Nat) (state work request gamma typ raw : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw))) :
    Nonempty (Derivation body Delta
      ((WorkAccepted H work).iff (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma]))) := by
  let P := WorkAccepted H work
  let Q := programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma]
  have hf : Nonempty (Derivation body (P :: Delta) Q) :=
    singletonToCheck H mode state work request gamma typ raw
      (withHyp hs P) (withHyp hc P) (withHyp hr P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (Q :: Delta) P) :=
    checkToSingleton H mode state work request gamma typ raw
      (withHyp hs Q) (withHyp hc Q) (withHyp hr Q)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem singletonIff (H : Program 1) (mode : Nat) (work request gamma typ raw : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw))) :
    Nonempty (Derivation body Delta
      ((WorkAccepted H work).iff (programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma]))) := by
  apply programCases InternalPairing.pairing (Fin.cons (numeral 1) (Fin.cons work Fin.elim0)) _
  intro beta j Theta state hj hs
  have hc' := renameInto hc j Theta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Theta hj
  simp only [stepRequestRename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at hr'
  simp only [consTermRename,emptyRename,oneRename] at hs
  change Nonempty (Derivation body Theta
    (((WorkAccepted H work).relabel j).iff
      ((programGraph (checkFor H mode) (numeral 1) ![typ,raw,gamma]).relabel j)))
  simp only [workAcceptedRename,programRename,oneRename,tripleRename]
  exact singletonAt H mode state (work.relabel j) (request.relabel j)
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) hs hc' hr'

theorem actualOriginalTypedInternalSingletonChecker :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalSingletonChecker := by
  constructor
  · intro body H alpha work request gamma typ raw
    let A := StepCons work request z ⊓ StepRequest request (numeral 0) gamma typ raw
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := singletonIff H 0 work request gamma typ raw (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction d⟩
  · intro body H alpha work request gamma types raw
    let A := StepCons work request z ⊓ StepRequest request (numeral 1) gamma types raw
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := singletonIff H 1 work request gamma types raw (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelSingletonProof
