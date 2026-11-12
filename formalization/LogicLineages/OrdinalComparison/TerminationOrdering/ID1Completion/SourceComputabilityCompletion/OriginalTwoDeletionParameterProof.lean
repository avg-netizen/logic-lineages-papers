module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextTwoDeletionInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionInternalStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (eqn)
open OriginalTwoDeletionParameterDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem inputSquare (gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight))) :
    Nonempty (Derivation body Delta
      (equal rawLeft rawRight ⊓ (equal paramLeft paramRight ⊓
        (graph2 InternalRawListRecursion.lookup a i upper ⊓
          graph2 InternalRawListRecursion.lookup b j lower)))) := by
  obtain ⟨hctx⟩ := OriginalContextTwoDeletionInductionProof.actualContextSquare
    body alpha Delta gamma count i j a b upper lower left right
  obtain ⟨hcf⟩ := andLeft hf
  have hc : Nonempty (Derivation body Delta
      (equal left right ⊓ (graph2 InternalRawListRecursion.lookup a i upper ⊓
        graph2 InternalRawListRecursion.lookup b j lower))) :=
    ⟨Derivation.implicationElimination hctx hcf⟩
  have hr := andRight hf
  have horder := andLeft (andRight (andLeft hf))
  have hraw := andIntro horder (andIntro (andLeft hr)
    (andIntro (andLeft (andRight hr))
      (andIntro (andLeft (andRight (andRight hr))) (andLeft (andRight (andRight (andRight hr)))))))
  obtain ⟨hraw⟩ := hraw
  obtain ⟨law⟩ := OriginalTwoDeletionInternalStatementChecks.actualPackedCommutation
    body alpha Delta raw a b i j rawUpper rawLower rawLeft rawRight
  have heRaw : Nonempty (Derivation body Delta (equal rawLeft rawRight)) :=
    ⟨Derivation.implicationElimination law hraw⟩
  have heCtx : Nonempty (Derivation body Delta (eqn left right)) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using andLeft hc
  have hparams := andRight (andRight (andRight (andRight hr)))
  have hleft := OriginalContextTwoDeletionCoreProof.secondInput
    InternalPairing.pairing paramLeft c left right heCtx (andLeft hparams)
  have hparam := valueUnique InternalPairing.pairing paramLeft paramRight
    (Fin.cons c (Fin.cons right Fin.elim0)) hleft (andRight hparams)
  have heParam : Nonempty (Derivation body Delta (equal paramLeft paramRight)) := by
    simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using hparam
  exact andIntro heRaw (andIntro heParam (andRight hc))

theorem actualInputSquare : OriginalTwoDeletionParameterTargets.ActualInputSquare := by
  intro body alpha Delta gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight
  let A := fields gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight
  obtain ⟨h⟩ := inputSquare (body := body) (Delta := A :: Delta) gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem sameInputs (R : Program 2) (x y p q u v : OTerm alpha)
    (hx : Nonempty (Derivation body Delta (equal x y)))
    (hp : Nonempty (Derivation body Delta (equal p q)))
    (hu : Nonempty (Derivation body Delta (graph2 R u x p)))
    (hv : Nonempty (Derivation body Delta (graph2 R v y q))) :
    Nonempty (Derivation body Delta (equal u v)) := by
  have hu' : Nonempty (Derivation body Delta (graph2 R u y q)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 Delta _ u
      (Fin.cons x (Fin.cons p Fin.elim0)) (Fin.cons y (Fin.cons q Fin.elim0)) _ hu
    intro t
    exact Fin.cases hx (Fin.cases hp (fun k => Fin.elim0 k)) t
  have he := valueUnique R u v (Fin.cons y (Fin.cons q Fin.elim0)) hu' hv
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,eqn] using he

theorem actualObservationSquare : OriginalTwoDeletionParameterTargets.ActualObservationSquare := by
  intro R body alpha Delta gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight valueLeft valueRight
  let A := fields gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight ⊓
    (graph2 R valueLeft rawLeft paramLeft ⊓ graph2 R valueRight rawRight paramRight)
  have hh : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hs := inputSquare gamma count i j a b upper lower left right raw rawUpper rawLower rawLeft rawRight c paramLeft paramRight (andLeft hh)
  obtain ⟨h⟩ := sameInputs R rawLeft rawRight paramLeft paramRight valueLeft valueRight
    (andLeft hs) (andLeft (andRight hs)) (andLeft (andRight hh)) (andRight (andRight hh))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTwoDeletionParameterProof
