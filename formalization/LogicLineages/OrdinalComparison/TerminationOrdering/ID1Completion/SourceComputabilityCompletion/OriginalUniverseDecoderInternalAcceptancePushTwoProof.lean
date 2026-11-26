module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePushProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePushTwoProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel OriginalUniverseDecoderInternalAcceptance
open OriginalUniverseDecoderInternalFuelSingletonSupportProof OriginalUniverseDecoderInternalFuelSingletonProof
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalAcceptanceSyntaxProof OriginalUniverseDecoderInternalAcceptanceStateProof
open OriginalUniverseDecoderInternalAcceptanceAppendProof
open OriginalTypedDecoderInternalAcceptanceCheckerProof
open OriginalTypedDecoderInternalScalarSyntaxProof OriginalTypedDecoderInternalRequestSyntaxProof
open OriginalTypedDecoderInternalRequestProof OriginalTypedDecoderInternalPushSyntaxProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem singletonForward (H : Program 1) (M W : Program 2) (mode : Nat) (work request gamma typ raw c : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M W work c))) :
    Nonempty (Derivation body Gamma (programGraph (checkFor H M W mode) (numeral 1) ![typ,raw,gamma,c])) := by
  obtain ⟨he⟩ := singletonIff H M W mode work request gamma typ raw c hc hr
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft he) ha⟩

theorem singletonBackward (H : Program 1) (M W : Program 2) (mode : Nat) (work request gamma typ raw c : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (StepCons work request z)))
    (hr : Nonempty (Derivation body Gamma (StepRequest request (numeral mode) gamma typ raw)))
    (ha : Nonempty (Derivation body Gamma (programGraph (checkFor H M W mode) (numeral 1) ![typ,raw,gamma,c]))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W work c)) := by
  obtain ⟨he⟩ := singletonIff H M W mode work request gamma typ raw c hc hr
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight he) ha⟩

theorem consAcceptedForward (H : Program 1) (M W : Program 2) (work request suffix singleton c : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (StepCons work request suffix)))
    (hs : Nonempty (Derivation body Gamma (StepCons singleton request z)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M W work c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W singleton c ⊓ WorkAccepted H M W suffix c)) := by
  obtain ⟨he⟩ := consIff H M W work request suffix singleton c hc hs
  obtain ⟨ha⟩ := ha
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft he) ha⟩

theorem consAcceptedBackward (H : Program 1) (M W : Program 2) (work request suffix singleton c : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (StepCons work request suffix)))
    (hs : Nonempty (Derivation body Gamma (StepCons singleton request z)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M W singleton c)))
    (hb : Nonempty (Derivation body Gamma (WorkAccepted H M W suffix c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W work c)) := by
  obtain ⟨he⟩ := consIff H M W work request suffix singleton c hc hs
  obtain ⟨hp⟩ := andIntro ha hb
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight he) hp⟩

theorem pushTwoAcceptedAt (H : Program 1) (M W : Program 2) (mode₁ mode₂ : Nat)
    (out gamma₁ typ₁ raw₁ gamma₂ typ₂ raw₂ request₁ request₂ tail work c : OTerm alpha)
    (h1 : Nonempty (Derivation body Gamma (StepRequest request₁ (numeral mode₁) gamma₁ typ₁ raw₁)))
    (h2 : Nonempty (Derivation body Gamma (StepRequest request₂ (numeral mode₂) gamma₂ typ₂ raw₂)))
    (hc2 : Nonempty (Derivation body Gamma (StepCons tail request₂ z)))
    (hc1 : Nonempty (Derivation body Gamma (StepCons work request₁ tail)))
    (hs : Nonempty (Derivation body Gamma (StepLive out work)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma
      (programGraph (checkFor H M W mode₁) (numeral 1) ![typ₁,raw₁,gamma₁,c] ⊓
        programGraph (checkFor H M W mode₂) (numeral 1) ![typ₂,raw₂,gamma₂,c])) := by
  have hw := acceptedStateAt H M W out work c hs ha
  apply programCases InternalListCodec.consCode (Fin.cons request₁ (Fin.cons z Fin.elim0)) _
  intro beta j Delta singleton hj hsingle
  simp only [conjunctionRename,programRename,oneRename,quadrupleRename]
  simp only [consTermRename,emptyRename,zRelabel] at hsingle
  have h1' := renameInto h1 j Delta hj
  have h2' := renameInto h2 j Delta hj
  simp only [stepRequestRename,numeralRename] at h1' h2'
  have hc1' := renameInto hc1 j Delta hj
  have hc2' := renameInto hc2 j Delta hj
  simp only [stepConsRename,zRelabel] at hc1' hc2'
  have hw' := renameInto hw j Delta hj
  rw [workAcceptedRename] at hw'
  have hsplit := consAcceptedForward H M W (work.relabel j) (request₁.relabel j) (tail.relabel j)
    singleton (c.relabel j) hc1' hsingle hw'
  exact andIntro
    (singletonForward H M W mode₁ singleton (request₁.relabel j) (gamma₁.relabel j)
      (typ₁.relabel j) (raw₁.relabel j) (c.relabel j) hsingle h1' (andLeft hsplit))
    (singletonForward H M W mode₂ (tail.relabel j) (request₂.relabel j) (gamma₂.relabel j)
      (typ₂.relabel j) (raw₂.relabel j) (c.relabel j) hc2' h2' (andRight hsplit))

theorem pushTwoAccepted (H : Program 1) (M W : Program 2) (mode₁ mode₂ : Nat)
    (out gamma₁ typ₁ raw₁ gamma₂ typ₂ raw₂ c : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma
      (StepPushTwo out (numeral mode₁) gamma₁ typ₁ raw₁ (numeral mode₂) gamma₂ typ₂ raw₂ z)))
    (ha : Nonempty (Derivation body Gamma (AcceptedState H M W out c))) :
    Nonempty (Derivation body Gamma
      (programGraph (checkFor H M W mode₁) (numeral 1) ![typ₁,raw₁,gamma₁,c] ⊓
        programGraph (checkFor H M W mode₂) (numeral 1) ![typ₂,raw₂,gamma₂,c])) := by
  apply stepPushTwoCases out (numeral mode₁) gamma₁ typ₁ raw₁ (numeral mode₂) gamma₂ typ₂ raw₂ z _ hp
  intro beta j Delta ys hj fields
  simp only [conjunctionRename,programRename,oneRename,quadrupleRename]
  have ha' := renameInto ha j Delta hj
  rw [acceptedStateRename] at ha'
  have h1 := andLeft fields
  have h2 := andLeft (andRight fields)
  simp only [numeralRename] at h1 h2
  have hc2 := andLeft (andRight (andRight fields))
  simp only [zRelabel] at hc2
  exact pushTwoAcceptedAt H M W mode₁ mode₂ (out.relabel j) (gamma₁.relabel j) (typ₁.relabel j)
    (raw₁.relabel j) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (c.relabel j) h1 h2 hc2
    (andLeft (andRight (andRight (andRight fields))))
    (andRight (andRight (andRight (andRight fields)))) ha'

def firstRequest (mode : Nat) : Program 6 :=
  pairOf (constant 6 mode) (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2)))
def secondRequest (mode : Nat) : Program 6 :=
  pairOf (constant 6 mode) (pairOf (.projection 3) (pairOf (.projection 4) (.projection 5)))
def firstWork (mode : Nat) : Program 6 := consOf (firstRequest mode) (constant 6 0)
def secondWork (mode : Nat) : Program 6 := consOf (secondRequest mode) (constant 6 0)
def joinedWork (first second : Nat) : Program 6 := consOf (firstRequest first) (secondWork second)
def pushQueries (first second : Nat) : Fin 6 → Program 6 :=
  ![firstRequest first,secondRequest second,firstWork first,secondWork second,
    joinedWork first second,OriginalTypedDecoder.liveOf (joinedWork first second)]

theorem acceptedPushTwoCases (H : Program 1) (M W : Program 2) (mode₁ mode₂ : Nat)
    (gamma₁ typ₁ raw₁ gamma₂ typ₂ raw₂ c : OTerm alpha) (psi : Formula alpha)
    (ha : Nonempty (Derivation body Gamma (programGraph (checkFor H M W mode₁) (numeral 1) ![typ₁,raw₁,gamma₁,c])))
    (hb : Nonempty (Derivation body Gamma (programGraph (checkFor H M W mode₂) (numeral 1) ![typ₂,raw₂,gamma₂,c])))
    (step : ∀ (beta : Type) (j : alpha → beta) (Delta : List (Formula beta)) (out : OTerm beta),
      (∀ q ∈ Gamma, q.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (StepPushTwo out (numeral mode₁)
        (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) (numeral mode₂)
        (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) z)) →
      Nonempty (Derivation body Delta (AcceptedState H M W out (c.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let xs : Fin 6 → OTerm alpha := Fin.cons gamma₁ (Fin.cons typ₁ (Fin.cons raw₁
    (Fin.cons gamma₂ (Fin.cons typ₂ (Fin.cons raw₂ Fin.elim0)))))
  apply queryCases (pushQueries mode₁ mode₂) xs _
  intro beta j ys Delta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 6 → OTerm beta := Fin.cons (gamma₁.relabel j) (Fin.cons (typ₁.relabel j)
    (Fin.cons (raw₁.relabel j) (Fin.cons (gamma₂.relabel j)
      (Fin.cons (typ₂.relabel j) (Fin.cons (raw₂.relabel j) Fin.elim0)))))
  have h1 := requestForward (constant 6 mode₁) (.projection 0) (.projection 1) (.projection 2)
    (ys 0) (numeral mode₁) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j) xx
    (constantValue mode₁ xx) (projectionValue 0 xx) (projectionValue 1 xx) (projectionValue 2 xx) (hq 0)
  have h2 := requestForward (constant 6 mode₂) (.projection 3) (.projection 4) (.projection 5)
    (ys 1) (numeral mode₂) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) xx
    (constantValue mode₂ xx) (projectionValue 3 xx) (projectionValue 4 xx) (projectionValue 5 xx) (hq 1)
  have hc1 := binaryRecover InternalListCodec.consCode (firstRequest mode₁) (constant 6 0)
    (ys 2) (ys 0) z xx (hq 2) (hq 0) (constantValue 0 xx)
  have hc2 := binaryRecover InternalListCodec.consCode (secondRequest mode₂) (constant 6 0)
    (ys 3) (ys 1) z xx (hq 3) (hq 1) (constantValue 0 xx)
  have hc := binaryRecover InternalListCodec.consCode (firstRequest mode₁) (secondWork mode₂)
    (ys 4) (ys 0) (ys 3) xx (hq 4) (hq 0) (hq 3)
  have hs := liveForward (joinedWork mode₁ mode₂) (ys 5) (ys 4) xx (hq 4) (hq 5)
  have ha' := renameInto ha j Delta hj
  have hb' := renameInto hb j Delta hj
  simp only [programRename,oneRename,quadrupleRename] at ha' hb'
  have wa := singletonBackward H M W mode₁ (ys 2) (ys 0) (gamma₁.relabel j)
    (typ₁.relabel j) (raw₁.relabel j) (c.relabel j) hc1 h1 ha'
  have wb := singletonBackward H M W mode₂ (ys 3) (ys 1) (gamma₂.relabel j)
    (typ₂.relabel j) (raw₂.relabel j) (c.relabel j) hc2 h2 hb'
  have hw := consAcceptedBackward H M W (ys 4) (ys 0) (ys 3) (ys 2) (c.relabel j) hc hc1 wa wb
  have hp := stepPushTwoIntro (ys 5) (numeral mode₁) (gamma₁.relabel j) (typ₁.relabel j) (raw₁.relabel j)
    (numeral mode₂) (gamma₂.relabel j) (typ₂.relabel j) (raw₂.relabel j) z
    (![ys 0,ys 1,ys 3,ys 4] : Fin 4 → OTerm beta)
    (andIntro h1 (andIntro h2 (andIntro hc2 (andIntro hc hs))))
  exact step beta j Delta (ys 5) hj hp (acceptedStateIntro H M W (ys 5) (ys 4) (c.relabel j) hs hw)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePushTwoProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptancePushTwoProof
