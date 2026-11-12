module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeChildTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCoprimeMultipleBoundedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseBoundsArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeChildProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport
open InternalTagArithmeticSyntaxProof (z suc)
open InternalAdditionLawsProof (add)
open InternalGraphCompositionFunctionalityProof
open InternalSquareRootArithmeticSupportProof (orderRight)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem unary (input child count childCount : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc z) input)))
    (hc : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) child input)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count input)))
    (hn : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw childCount child))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess childCount count)) := by
  obtain ⟨he⟩ := valueUnique OriginalStructuralNodeSize.raw (suc childCount) count ![input]
    (OriginalStructuralNodeSizeInternalRecurrenceProof.unary input child childCount ha hc hn) hp
  obtain ⟨hlt⟩ := InternalCoprimeMultipleBoundedProof.selfLtSucc (body := body) (Gamma := Delta) childCount
  exact ⟨orderRight childCount he hlt⟩

theorem binary (input first second count firstCount secondCount : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (suc (suc z)) input)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first input)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second input)))
    (hp : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw count input)))
    (hfc : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw firstCount first)))
    (hsc : Nonempty (Derivation body Delta (graph1 OriginalStructuralNodeSize.raw secondCount second))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess firstCount count ⊓ InternalLessThan.strictLess secondCount count)) := by
  obtain ⟨he⟩ := valueUnique OriginalStructuralNodeSize.raw (suc (add firstCount secondCount)) count ![input]
    (OriginalStructuralNodeSizeInternalRecurrenceProof.binary input first second firstCount secondCount ha hf hs hfc hsc) hp
  obtain ⟨hf⟩ := InternalUnpairArithmeticProof.leftWeakAdd (body := body) (Gamma := Delta) firstCount secondCount
  obtain ⟨hs⟩ := InternalUnpairReverseBoundsArithmeticProof.rightWeakAdd (body := body) (Gamma := Delta) firstCount secondCount
  exact andIntro ⟨orderRight firstCount he hf⟩ ⟨orderRight secondCount he hs⟩

theorem actualUnary : OriginalStructuralNodeSizeChildTargets.UnaryChildStrict := by
  intro body alpha Delta input child count childCount
  let A := graph1 (arityOf (.projection 0)) (suc z) input ⊓
    (graph1 (firstOf (.projection 0)) child input ⊓
      (graph1 OriginalStructuralNodeSize.raw count input ⊓ graph1 OriginalStructuralNodeSize.raw childCount child))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := unary input child count childCount (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andRight (andRight (andRight h)))
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualBinary : OriginalStructuralNodeSizeChildTargets.BinaryChildrenStrict := by
  intro body alpha Delta input first second count firstCount secondCount
  let A := graph1 (arityOf (.projection 0)) (suc (suc z)) input ⊓
    (graph1 (firstOf (.projection 0)) first input ⊓
      (graph1 (secondOf (.projection 0)) second input ⊓
        (graph1 OriginalStructuralNodeSize.raw count input ⊓
          (graph1 OriginalStructuralNodeSize.raw firstCount first ⊓ graph1 OriginalStructuralNodeSize.raw secondCount second))))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := binary input first second count firstCount secondCount (andLeft h) (andLeft (andRight h))
    (andLeft (andRight (andRight h))) (andLeft (andRight (andRight (andRight h))))
    (andLeft (andRight (andRight (andRight (andRight h)))))
    (andRight (andRight (andRight (andRight (andRight h)))))
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeChildProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeChildProof
