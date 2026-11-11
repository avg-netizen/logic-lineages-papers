module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceBinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinalApplicationAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalTransparentLambdaValidityInternalLambdaSupportProof (addAssumption)
open InternalApplicationValidityClosure
open OriginalTransparentDecoderValidatorCollapse
open OriginalTransparentDecoderValidatorCollapseInduction
open OriginalHereditaryValidity OriginalTransparentLambdaValidity
open OriginalTransparentLambdaFinalApplicationSelectorProof
open OriginalTransparentLambdaFinalApplicationNodeProof
open OriginalTransparentLambdaFinalApplicationAcceptanceProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- The guarded original source checker has exactly the same two packed
children. Their retained context guard supplies G in the reverse direction. -/
theorem sourceApplicationCoordinatesIff (H G : Program 1) (M W : Program 2)
    (packed parameter typ raw middle d fp ap arrow fn arg c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hn : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) middle)))
    (hb : Nonempty (Derivation body Gamma (StepBinaryPayload middle d fp ap)))
    (har : Nonempty (Derivation body Gamma (StepCons arrow d typ)))
    (hfn : Nonempty (Derivation body Gamma (StepPair fn arrow fp)))
    (harg : Nonempty (Derivation body Gamma (StepPair arg d ap)))
    (hparam : Nonempty (Derivation body Gamma (StepPair parameter c gamma))) :
    Nonempty (Derivation body Gamma
      ((graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter).iff
        (graph2 M (numeral 1) typ c ⊓
          (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) fn parameter ⊓
            graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) arg parameter)))) := by
  let S := OriginalUniverseDecoder.source H G M W
  let A := graph2 S (numeral 1) packed parameter
  let B := graph2 M (numeral 1) typ c ⊓
    (graph2 S (numeral 1) fn parameter ⊓ graph2 S (numeral 1) arg parameter)
  have hrec := OriginalUniverseDecoderInternalAcceptanceBinaryProof.applicationIff
    H M W raw middle d fp ap typ arrow gamma c hn hb har
  have forward : Nonempty (Derivation body (A :: Gamma) B) := by
    have fields := sourceFieldsElim H G M W packed parameter typ raw c gamma
      (addAssumption hp A) (addAssumption hparam A)
      (show Nonempty (Derivation body (A :: Gamma) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hrec'⟩ := addAssumption hrec A
    obtain ⟨ha⟩ := andRight fields
    have factors : Nonempty (Derivation body (A :: Gamma)
        (graph2 M (numeral 1) typ c ⊓
          (OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W arrow fp gamma c ⊓
            OriginalUniverseDecoderInternalAcceptance.TermAccepted H M W d ap gamma c))) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hrec') ha⟩
    exact andIntro (andLeft factors) (andIntro
      (sourceFieldsIntro H G M W fn parameter arrow fp c gamma
        (addAssumption hfn A) (addAssumption hparam A) (andLeft fields) (andLeft (andRight factors)))
      (sourceFieldsIntro H G M W arg parameter d ap c gamma
        (addAssumption harg A) (addAssumption hparam A) (andLeft fields) (andRight (andRight factors))))
  have backward : Nonempty (Derivation body (B :: Gamma) A) := by
    have h : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have ffields := sourceFieldsElim H G M W fn parameter arrow fp c gamma
      (addAssumption hfn B) (addAssumption hparam B) (andLeft (andRight h))
    have afields := sourceFieldsElim H G M W arg parameter d ap c gamma
      (addAssumption harg B) (addAssumption hparam B) (andRight (andRight h))
    obtain ⟨hrec'⟩ := addAssumption hrec B
    obtain ⟨hfactors⟩ := andIntro (andLeft h) (andIntro (andRight ffields) (andRight afields))
    exact sourceFieldsIntro H G M W packed parameter typ raw c gamma
      (addAssumption hp B) (addAssumption hparam B) (andLeft ffields)
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hrec') hfactors⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

/-- The constructor step consumes only the two smaller-payload induction
instances. Every type and runtime parameter is retained literally. -/
theorem sourceApplicationAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (packed parameter typ raw middle d fp ap arrow fn arg c gamma : OTerm alpha)
    (hp : Nonempty (Derivation body Gamma (StepPair packed typ raw)))
    (hn : Nonempty (Derivation body Gamma (StepPair raw (numeral 2) middle)))
    (hb : Nonempty (Derivation body Gamma (StepBinaryPayload middle d fp ap)))
    (hc : Nonempty (Derivation body Gamma (applicationConstructors arrow d typ fp ap fn arg packed)))
    (hparam : Nonempty (Derivation body Gamma (StepPair parameter c gamma)))
    (hfi : Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource fn parameter)))
    (hai : Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource arg parameter))) :
    Nonempty (Derivation body Gamma
      (Acceptance (sourceValidator (refined p H G W).base) (transparent p H G W).base.oldSource packed parameter)) := by
  let N := normalizedData (refined p H G W).base
  let S := (transparent p H G W).base.oldSource
  let V := sourceValidator (refined p H G W).base
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  have ht := rawTypeAndTag arrow d typ fp ap fn arg packed hc
  have hval := acceptanceAtChildren (sourceRoot N) (targetRoot N) N.member N.member
    packed parameter typ fn arg (andRight ht)
    (sourceApplicationNode N packed parameter typ (andLeft ht) (andRight ht))
    (childrenEquation (sourceRoot N) (targetRoot N) N.member arrow d typ fp ap fn arg packed parameter hc)
  have hsrc := sourceApplicationCoordinatesIff H G M W packed parameter typ raw middle d fp ap arrow fn arg c gamma
    hp hn hb (andLeft hc) (andLeft (andRight hc)) (andLeft (andRight (andRight hc))) hparam
  let A := graph2 V (numeral 1) packed parameter
  let B := graph2 S (numeral 1) packed parameter
  have forward : Nonempty (Derivation body (A :: Gamma) B) := by
    obtain ⟨hv⟩ := addAssumption hval A
    have factors : Nonempty (Derivation body (A :: Gamma)
        (graph2 N.member (numeral 1) typ parameter ⊓
          (graph2 V (numeral 1) fn parameter ⊓ graph2 V (numeral 1) arg parameter))) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hv) (Derivation.hypothesis List.mem_cons_self)⟩
    obtain ⟨hfi'⟩ := addAssumption hfi A
    obtain ⟨hai'⟩ := addAssumption hai A
    obtain ⟨hf⟩ := andLeft (andRight factors)
    obtain ⟨ha⟩ := andRight (andRight factors)
    have hm := InternalOriginalUniformContextMembershipInternalProof.sliceRecover p.base.member
      (numeral 1) typ parameter c gamma (addAssumption hparam A) (andLeft factors)
    obtain ⟨hparts⟩ := andIntro hm (andIntro
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hfi') hf⟩
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hai') ha⟩)
    obtain ⟨hs⟩ := addAssumption hsrc A
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hs) hparts⟩
  have backward : Nonempty (Derivation body (B :: Gamma) A) := by
    obtain ⟨hs⟩ := addAssumption hsrc B
    have factors : Nonempty (Derivation body (B :: Gamma)
        (graph2 M (numeral 1) typ c ⊓
          (graph2 S (numeral 1) fn parameter ⊓ graph2 S (numeral 1) arg parameter))) :=
      ⟨Derivation.implicationElimination (Derivation.conjunctionLeft hs) (Derivation.hypothesis List.mem_cons_self)⟩
    obtain ⟨hfi'⟩ := addAssumption hfi B
    obtain ⟨hai'⟩ := addAssumption hai B
    obtain ⟨hf⟩ := andLeft (andRight factors)
    obtain ⟨ha⟩ := andRight (andRight factors)
    have hm := InternalOriginalUniformContextMembershipInternalProof.sliceAccept p.base.member
      (numeral 1) typ parameter c gamma (addAssumption hparam B) (andLeft factors)
    obtain ⟨hparts⟩ := andIntro hm (andIntro
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hfi') hf⟩
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hai') ha⟩)
    obtain ⟨hv⟩ := addAssumption hval B
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hv) hparts⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceApplicationProof
