module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalUniverseDecoderInternalFuelSingletonSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem quadrupleRename {beta : Type} (typ raw gamma c : OTerm alpha) (j : alpha → beta) :
    (fun i : Fin 4 => (![typ,raw,gamma,c] i).relabel j) =
      ![typ.relabel j,raw.relabel j,gamma.relabel j,c.relabel j] := by
  funext i
  refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i

theorem singletonAt (H : Program 1) (M contextWindow : Program 2) (mode : Nat) (state work request gamma typ raw c : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StepLive state work)))
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw))) :
    Nonempty (Derivation body Delta
      ((WorkAccepted H M contextWindow work c).iff (programGraph (checkFor H M contextWindow mode) (numeral 1) ![typ,raw,gamma,c]))) := by
  let P := WorkAccepted H M contextWindow work c
  let Q := programGraph (checkFor H M contextWindow mode) (numeral 1) ![typ,raw,gamma,c]
  have hf : Nonempty (Derivation body (P :: Delta) Q) :=
    singletonToCheck H M contextWindow mode state work request gamma typ raw c
      (withHyp hs P) (withHyp hc P) (withHyp hr P)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body (Q :: Delta) P) :=
    checkToSingleton H M contextWindow mode state work request gamma typ raw c
      (withHyp hs Q) (withHyp hc Q) (withHyp hr Q)
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

theorem singletonIff (H : Program 1) (M contextWindow : Program 2) (mode : Nat) (work request gamma typ raw c : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (StepCons work request z)))
    (hr : Nonempty (Derivation body Delta (StepRequest request (numeral mode) gamma typ raw))) :
    Nonempty (Derivation body Delta
      ((WorkAccepted H M contextWindow work c).iff (programGraph (checkFor H M contextWindow mode) (numeral 1) ![typ,raw,gamma,c]))) := by
  apply programCases InternalPairing.pairing (Fin.cons (numeral 1) (Fin.cons work Fin.elim0)) _
  intro beta j Theta state hj hs
  have hc' := renameInto hc j Theta hj
  simp only [stepConsRename,zRelabel] at hc'
  have hr' := renameInto hr j Theta hj
  simp only [stepRequestRename,OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at hr'
  simp only [consTermRename,emptyRename,oneRename] at hs
  change Nonempty (Derivation body Theta
    (((WorkAccepted H M contextWindow work c).relabel j).iff
      ((programGraph (checkFor H M contextWindow mode) (numeral 1) ![typ,raw,gamma,c]).relabel j)))
  simp only [workAcceptedRename,programRename,oneRename,quadrupleRename]
  exact singletonAt H M contextWindow mode state (work.relabel j) (request.relabel j)
    (gamma.relabel j) (typ.relabel j) (raw.relabel j) (c.relabel j) hs hc' hr'

theorem actualOriginalUniverseInternalSingletonChecker :
    OriginalUniverseDecoderInternalFuelTargets.ActualOriginalUniverseInternalSingletonChecker := by
  constructor
  · intro body H M contextWindow alpha work request gamma typ raw c
    let A := StepCons work request z ⊓ StepRequest request (numeral 0) gamma typ raw
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := singletonIff H M contextWindow 0 work request gamma typ raw c (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction d⟩
  · intro body H M contextWindow alpha work request gamma types raw c
    let A := StepCons work request z ⊓ StepRequest request (numeral 1) gamma types raw
    have h : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := singletonIff H M contextWindow 1 work request gamma types raw c (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelSingletonProof
