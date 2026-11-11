module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorArityCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalPairingSumBounds InternalApplicationCertifiedResultFoldClosure
open InternalTagArithmeticSyntaxProof (suc z)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalConstructorArityCasesProof
open OriginalRawSyntaxTransportInternalConstructorSelectorBoundsProof
open OriginalRawSyntaxTransportInternalConstructorSelectorEliminationProof
open OriginalLambdaTraversalInternalPayloadArithmeticProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- All raw unary nodes satisfy the original strict child budget. There is no
source constructor, well-typedness or external numeric-bound premise. -/
theorem unaryChildBound (raw child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) child raw))) :
    Nonempty (Derivation body Delta (weakBound (suc child) raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  apply orCases (arityOneTags raw ha)
  · intro Theta inc ht
    have htag := unaryValue InternalUnpair.left (.projection 0) (numeral 1) raw xs ht (projectionValue 0 xs)
    exact unarySelectorsBound 1 (by decide) raw child ht
      (firstTag1 (.projection 0) child xs htag (weakenProof hf inc))
  · intro Theta inc ht
    have htag := unaryValue InternalUnpair.left (.projection 0) (numeral 4) raw xs ht (projectionValue 0 xs)
    exact unarySelectorsBound 4 (by decide) raw child ht
      (firstTag4 (.projection 0) child xs htag (weakenProof hf inc))

/-- All raw binary nodes retain first-before-second order, including numbered
base/extras, in the exact child-sum budget. -/
theorem binaryChildBound (raw first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta (weakBound (childFuelSum first second) raw)) := by
  let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
  apply orCases (arityTwoTags raw ha)
  · intro Theta inc ht
    have htag := unaryValue InternalUnpair.left (.projection 0) (numeral 2) raw xs ht (projectionValue 0 xs)
    exact binarySelectorsBound 2 (by decide) raw first second ht
      (firstTag2 (.projection 0) first xs htag (weakenProof hf inc))
      (secondTag2 (.projection 0) second xs htag (weakenProof hs inc))
  · intro Theta inc ht
    apply orCases ht
    · intro Xi inc' ht'
      have hm : ∀ a ∈ Delta, a ∈ Xi := fun a ha => inc' a (inc a ha)
      have htag := unaryValue InternalUnpair.left (.projection 0) (numeral 5) raw xs ht' (projectionValue 0 xs)
      exact numberedSelectorsBound raw first second ht'
        (firstTag5 (.projection 0) first xs htag (weakenProof hf hm))
        (secondTag5 (.projection 0) second xs htag (weakenProof hs hm))
    · intro Xi inc' ht'
      have hm : ∀ a ∈ Delta, a ∈ Xi := fun a ha => inc' a (inc a ha)
      have htag := unaryValue InternalUnpair.left (.projection 0) (numeral 7) raw xs ht' (projectionValue 0 xs)
      exact binarySelectorsBound 7 (by decide) raw first second ht'
        (firstTag7 (.projection 0) first xs htag (weakenProof hf hm))
        (secondTag7 (.projection 0) second xs htag (weakenProof hs hm))

theorem unaryChildStrict (raw child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) child raw))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess child raw)) :=
  lambdaDescent raw child (unaryChildBound raw child ha hf)

theorem binaryChildrenStrict (raw first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta
      (InternalLessThan.strictLess first raw ⊓ InternalLessThan.strictLess second raw)) :=
  applicationDescent raw first second (binaryChildBound raw first second ha hf hs)

/-- The bound is the SAME literal 2*raw+1 budget used by the frozen machine. -/
theorem unaryFuelBound (raw child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 1) raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) child raw))) :
    Nonempty (Derivation body Delta
      (weakBound (suc (suc (payloadFuel child))) (payloadFuel raw))) :=
  lambdaFuel raw child (unaryChildBound raw child ha hf)

theorem binaryFuelBound (raw first second : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph1 (arityOf (.projection 0)) (numeral 2) raw)))
    (hf : Nonempty (Derivation body Delta (graph1 (firstOf (.projection 0)) first raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (secondOf (.projection 0)) second raw))) :
    Nonempty (Derivation body Delta (weakBound
      (suc (add (payloadFuel first) (add (payloadFuel second) (suc z)))) (payloadFuel raw))) :=
  applicationFuel raw first second (binaryChildBound raw first second ha hf hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorBoundsProof
