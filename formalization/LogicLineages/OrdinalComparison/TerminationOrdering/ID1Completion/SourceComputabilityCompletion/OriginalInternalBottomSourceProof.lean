module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceMemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceLeafProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSourceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalAcceptanceSupportProof (programCases)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalScalarSyntaxProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atPayload (H G : Program 1) (M W : Program 2) (s t parameter typ raw c gamma payload : OTerm alpha)
 (hv : Nonempty (Derivation body Delta (graph1 BottomSourceShapeProof.bottomPayload payload typ)))
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter)))
 (hp : Nonempty (Derivation body Delta (StepPair s typ raw)))
 (hparam : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ))) :
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)) := by
 have hfields := sourceFieldsElim H G M W s parameter typ raw c gamma hp hparam hs
 have hm := OriginalInternalBottomSourceMemberProof.termMembership H M W typ raw gamma c (andRight hfields)
 have hg := andLeft hfields
 let xs : Fin 1 → OTerm alpha := ![typ]
 have hraw := binaryRecover InternalPairing.pairing (BottomRepresentative.constant 3) (.projection 0)
  payload (numeral 3) (typ) xs hv
  (BottomSourceValidityProof.constantValue 3 xs) (projectionValue 0 xs)
 have hpacked := binaryRecover InternalPairing.pairing (.projection 0) BottomSourceShapeProof.bottomPayload
  (t) (typ) payload xs hb (projectionValue 0 xs) hv
 have hi := OriginalUniverseDecoderInternalAcceptanceLeafProof.bottomIff H M W payload (typ) (typ)
  (gamma) (c) hraw
 have he : Nonempty (Derivation body Delta (equal (typ) (typ))) := by
  rw [InternalControlGraphSupportProof.equalEqn]
  exact ⟨InternalTagArithmeticSupportProof.refl _⟩
 obtain ⟨hib⟩ := andRight hi
 obtain ⟨prem⟩ := andIntro hm he
 exact sourceFieldsIntro H G M W (t) (parameter) (typ) payload
  (c) (gamma) hpacked hparam hg ⟨Derivation.implicationElimination hib prem⟩

theorem atPairs (H G : Program 1) (M W : Program 2) (s t parameter typ raw c gamma : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) s parameter)))
 (hp : Nonempty (Derivation body Delta (StepPair s typ raw)))
 (hparam : Nonempty (Derivation body Delta (StepPair parameter c gamma)))
 (hb : Nonempty (Derivation body Delta (graph1 BottomRepresentative.bottomCode t typ))) :
 Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)) := by
 apply programCases BottomSourceShapeProof.bottomPayload ![typ]
  (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) t parameter)
 intro beta j Theta payload hj hv
 simp only [graph2Rename,numeralRename]
 have hs' := renameInto hs j Theta hj
 have hb' := renameInto hb j Theta hj
 have hp' := renameInto hp j Theta hj
 have hparam' := renameInto hparam j Theta hj
 simp only [graph2Rename,numeralRename] at hs'
 simp only [graph1Rename] at hb'
 simp only [stepPairRename] at hp' hparam'
 exact atPayload H G M W (s.relabel j) (t.relabel j) (parameter.relabel j) (typ.relabel j)
  (raw.relabel j) (c.relabel j) (gamma.relabel j) payload hv hs' hp' hparam' hb'

theorem bottomSource : OriginalInternalBottomSourceTargets.ActualBottomSource := by
 intro H G M W body alpha Delta s t parameter typ hs htype hb
 let qs : Fin 3 → Program 2 := ![InternalApplicationCertificateConstructors.rightOf (.projection 0),
  InternalApplicationCertificateConstructors.leftOf (.projection 1),InternalApplicationCertificateConstructors.rightOf (.projection 1)]
 let xs : Fin 2 → OTerm alpha := ![s,parameter]
 apply queryCases qs xs _
 intro beta j ys Theta hj hq
 simp only [graph2Rename,numeralRename]
 have hs' := renameInto hs j Theta hj
 have ht' := renameInto htype j Theta hj
 have hb' := renameInto hb j Theta hj
 simp only [graph2Rename,numeralRename] at hs'
 simp only [graph1Rename] at ht' hb'
 let xx : Fin 2 → OTerm beta := ![s.relabel j,parameter.relabel j]
 have hx : (fun i => (xs i).relabel j) = xx := by funext i; exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have hq' (i : Fin 3) : Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by simpa only [hx] using hq i
 have hr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (s.relabel j) xx (hq' 0) (projectionValue 0 xx)
 have hc := unaryRecover InternalUnpair.left (.projection 1) (ys 1) (parameter.relabel j) xx (hq' 1) (projectionValue 1 xx)
 have hg := unaryRecover InternalUnpair.right (.projection 1) (ys 2) (parameter.relabel j) xx (hq' 2) (projectionValue 1 xx)
 exact atPairs H G M W (s.relabel j) (t.relabel j) (parameter.relabel j) (typ.relabel j) (ys 0) (ys 1) (ys 2)
  hs' (reconstructPair _ _ _ ht' hr) (reconstructPair _ _ _ hc hg) hb'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceProof
