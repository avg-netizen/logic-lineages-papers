module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight queryCases)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTypedDecoderInternalScalarProof OriginalTypedDecoderInternalRequestSelectorsProof
open OriginalUniverseDecoderInternalSyntaxProof OriginalUniverseDecoderInternalAcceptanceProof
open OriginalUniverseDecoderInternalDecisionProof
open OriginalUniverseDecoder OriginalUniverseDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Reconstruct the five actual guard selectors from one literal request and
three original raw pair relations. Gamma is only an untouched codec field. -/
theorem prefixSelectors (r c m g t rawCode v p d rest h tail : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (StepRequest r m g t rawCode)))
    (hp : Nonempty (Derivation body Delta (StepPair rawCode v p)))
    (hd : Nonempty (Derivation body Delta (StepPair p d rest)))
    (hh : Nonempty (Derivation body Delta (StepPair rest h tail))) :
    Nonempty (Derivation body Delta (graph2 mode m r c)) ∧
      Nonempty (Derivation body Delta (graph2 typ t r c)) ∧
      Nonempty (Derivation body Delta (graph2 tag v r c)) ∧
      Nonempty (Derivation body Delta (graph2 domain d r c)) ∧
      Nonempty (Derivation body Delta (graph2 numberedHead h r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  have hf := fun i => requestFieldValue request i r m g t rawCode xs (projectionValue 0 xs) hr
  have hv := pairLeftValue raw rawCode v p xs (hf 3) hp
  have hpay := pairRightValue raw rawCode v p xs (hf 3) hp
  have hdomain := pairLeftValue payload p d rest xs hpay hd
  have hrest := pairRightValue payload p d rest xs hpay hd
  have hhead := pairLeftValue (rightOf payload) rest h tail xs hrest hh
  exact ⟨hf 0,hf 2,hv,hdomain,hhead⟩

/-- Internally supply all ten arithmetic witnesses from the SAME request,
including arbitrary malformed numeric requests. -/
theorem guardForward (M W : Program 2) (out r c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.guard M W) out r c))) :
    Nonempty (Derivation body Delta (guardSpec M W out r c)) := by
  let qs : Fin 10 → Program 2 :=
    ![mode,leftOf (rightOf request),typ,raw,tag,payload,domain,rightOf payload,numberedHead,rightOf (rightOf payload)]
  apply queryCases qs (![r,c] : Fin 2 → OTerm alpha) _
  intro beta j ys Theta hj hq
  rw [guardRename]
  have ho' := renameInto ho j Theta hj
  rw [graph2Rename] at ho'
  simp only [Matrix.vecCons,Matrix.vecEmpty,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := ![r.relabel j,c.relabel j]
  have hr := requestFields request (r.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) xx
    (projectionValue 0 xx) (hq 0) (hq 1) (hq 2) (hq 3)
  have hp := pairFields raw (ys 3) (ys 4) (ys 5) xx (hq 3) (hq 4) (hq 5)
  have hd := pairFields payload (ys 5) (ys 6) (ys 7) xx (hq 5) (hq 6) (hq 7)
  have hh := pairFields (rightOf payload) (ys 7) (ys 8) (ys 9) xx (hq 7) (hq 8) (hq 9)
  have hi := acceptEquivalence M W (r.relabel j) (c.relabel j) (ys 0) (ys 2) (ys 4) (ys 6) (ys 8)
    (hq 0) (hq 2) (hq 4) (hq 6) (hq 8)
  have hc := decisionForward (guardBoolean M W) (out.relabel j) xx
    (guardCondition M W (ys 0) (ys 2) (ys 4) (ys 6) (ys 8) (c.relabel j)) hi ho'
  exact guardIntro M W _ _ _ ys (andIntro hr (andIntro hp (andIntro hd (andIntro hh hc))))

/-- Reverse the independent frozen arithmetic formula at every output.
In particular a false condition constructs the actual zero graph. -/
theorem guardBackward (M W : Program 2) (out r c : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (guardSpec M W out r c))) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.guard M W) out r c)) := by
  apply guardCases M W out r c _ ho
  intro beta j Theta ys hj hq
  rw [graph2Rename]
  have hs := prefixSelectors (r.relabel j) (c.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9)
    (andLeft hq) (andLeft (andRight hq)) (andLeft (andRight (andRight hq)))
    (andLeft (andRight (andRight (andRight hq))))
  let xx : Fin 2 → OTerm beta := ![r.relabel j,c.relabel j]
  have hi := acceptEquivalence M W (r.relabel j) (c.relabel j) (ys 0) (ys 2) (ys 4) (ys 6) (ys 8)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  exact decisionBackward (guardBoolean M W) (out.relabel j) xx
    (guardCondition M W (ys 0) (ys 2) (ys 4) (ys 6) (ys 8) (c.relabel j)) hi
    (andRight (andRight (andRight (andRight hq))))

theorem guardEquivalence (M W : Program 2) (out r c : OTerm alpha) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalUniverseDecoder.guard M W) out r c).iff (guardSpec M W out r c))) := by
  obtain ⟨hf⟩ := guardForward (body := body) (Delta := graph2 (OriginalUniverseDecoder.guard M W) out r c :: Delta)
    M W out r c ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := guardBackward (body := body) (Delta := guardSpec M W out r c :: Delta)
    M W out r c ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalGuardProof
