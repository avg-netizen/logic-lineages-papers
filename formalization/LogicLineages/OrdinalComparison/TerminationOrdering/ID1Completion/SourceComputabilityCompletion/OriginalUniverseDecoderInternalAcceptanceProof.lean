module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalExtraProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalDecisionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (andIntro andLeft andRight)
open InternalOriginalPairingOrderArithmeticProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalTypedDecoder (ifSame)
open OriginalTypedDecoderInternalBranchProof OriginalUniverseDecoderInternalBooleanProof
open OriginalUniverseDecoderInternalExtraProof OriginalUniverseDecoderInternalDecisionProof
open OriginalUniverseDecoder OriginalUniverseDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem guardBoolean (M W : Program 2) : BooleanTree (OriginalUniverseDecoder.guard M W) := by
  apply BooleanTree.branch
  · apply BooleanTree.branch
    · apply BooleanTree.branch
      · exact BooleanTree.branch _ _ _ _ BooleanTree.one BooleanTree.zero
      · apply BooleanTree.branch
        · exact BooleanTree.branch _ _ _ _ BooleanTree.one BooleanTree.zero
        · apply BooleanTree.branch
          · exact BooleanTree.branch _ _ _ _ BooleanTree.one BooleanTree.zero
          · exact BooleanTree.one
    · exact BooleanTree.zero
  · exact BooleanTree.branch _ _ _ _ BooleanTree.one BooleanTree.zero

theorem acceptForward (M W : Program 2) (r c m t v d h : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 mode m r c)))
    (ht : Nonempty (Derivation body Delta (graph2 typ t r c)))
    (hv : Nonempty (Derivation body Delta (graph2 tag v r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (hh : Nonempty (Derivation body Delta (graph2 numberedHead h r c)))
    (ho : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) r c))) :
    Nonempty (Derivation body Delta (guardCondition M W m t v d h c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  let root := ifSame (memberAt M typ) (constant 2 1) (extraGuard M W) (constant 2 0)
  let other := ifSame mode (constant 2 1) (constant 2 1) (constant 2 0)
  apply formulaCases (equal m (numeral 0)) _
  · have he : Nonempty (Derivation body (equal m (numeral 0) :: Delta) (equal m (numeral 0))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hg := sameYesElim mode (constant 2 0) root other (numeral 1) m (numeral 0) xs
      (withHyp hm _) (constantValue 0 xs) he (withHyp ho _)
    have hparts := filterForward (memberAt M typ) (extraGuard M W) xs hg
    have hroot := binaryRecover M typ context (numeral 1) t c xs (andLeft hparts)
      (withHyp ht _) (projectionValue 1 xs)
    have hextra := extraForward M W r c v d h (withHyp hv _) (withHyp hd _) (withHyp hh _) (andRight hparts)
    obtain ⟨hgood⟩ := andIntro he (andIntro hroot hextra)
    exact ⟨orLeft hgood⟩
  · have hn : Nonempty (Derivation body ((equal m (numeral 0)).not :: Delta) (equal m (numeral 0)).not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hg := sameNoElim mode (constant 2 0) root other (numeral 1) m (numeral 0) xs
      (withHyp hm _) (constantValue 0 xs) hn (withHyp ho _)
    have hparts := filterForward mode (constant 2 1) xs hg
    obtain ⟨he⟩ := valueUnique mode m (numeral 1) xs (withHyp hm _) (andLeft hparts)
    exact ⟨orRight (by simpa only [equalEqn] using he)⟩

theorem acceptBackward (M W : Program 2) (r c m t v d h : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 mode m r c)))
    (ht : Nonempty (Derivation body Delta (graph2 typ t r c)))
    (hv : Nonempty (Derivation body Delta (graph2 tag v r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (hh : Nonempty (Derivation body Delta (graph2 numberedHead h r c)))
    (ho : Nonempty (Derivation body Delta (guardCondition M W m t v d h c))) :
    Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) r c)) := by
  let xs : Fin 2 → OTerm alpha := ![r,c]
  let root := ifSame (memberAt M typ) (constant 2 1) (extraGuard M W) (constant 2 0)
  let other := ifSame mode (constant 2 1) (constant 2 1) (constant 2 0)
  let C := equal m (numeral 0) ⊓ (graph2 M (numeral 1) t c ⊓ extraCondition M W v d h c)
  apply orCases ho
  · have hc : Nonempty (Derivation body (C :: Delta) C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply sameYesIntro mode (constant 2 0) root other (numeral 1) m (numeral 0) xs
      (withHyp hm _) (constantValue 0 xs) (andLeft hc)
    apply filterBackward (memberAt M typ) (extraGuard M W) xs
    · exact binaryValue M typ context (numeral 1) t c xs (andLeft (andRight hc)) (withHyp ht _) (projectionValue 1 xs)
    · exact extraBackward M W r c v d h (withHyp hv _) (withHyp hd _) (withHyp hh _) (andRight (andRight hc))
  · have hc : Nonempty (Derivation body (equal m (numeral 1) :: Delta) (equal m (numeral 1))) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    apply sameNoIntro mode (constant 2 0) root other (numeral 1) m (numeral 0) xs
      (withHyp hm _) (constantValue 0 xs) (excludeNumeral m 1 0 (by decide) hc)
    exact sameYesIntro mode (constant 2 1) (constant 2 1) (constant 2 0) (numeral 1) m (numeral 1) xs
      (withHyp hm _) (constantValue 1 xs) hc (constantValue 1 xs)

theorem acceptEquivalence (M W : Program 2) (r c m t v d h : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 mode m r c)))
    (ht : Nonempty (Derivation body Delta (graph2 typ t r c)))
    (hv : Nonempty (Derivation body Delta (graph2 tag v r c)))
    (hd : Nonempty (Derivation body Delta (graph2 domain d r c)))
    (hh : Nonempty (Derivation body Delta (graph2 numberedHead h r c))) :
    Nonempty (Derivation body Delta
      ((graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) r c).iff (guardCondition M W m t v d h c))) := by
  obtain ⟨hf⟩ := acceptForward M W r c m t v d h
    (withHyp hm _) (withHyp ht _) (withHyp hv _) (withHyp hd _) (withHyp hh _)
    (show Nonempty (Derivation body ((graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) r c) :: Delta)
      (graph2 (OriginalUniverseDecoder.guard M W) (numeral 1) r c)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := acceptBackward M W r c m t v d h
    (withHyp hm _) (withHyp ht _) (withHyp hv _) (withHyp hd _) (withHyp hh _)
    (show Nonempty (Derivation body (guardCondition M W m t v d h c :: Delta)
      (guardCondition M W m t v d h c)) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceProof
