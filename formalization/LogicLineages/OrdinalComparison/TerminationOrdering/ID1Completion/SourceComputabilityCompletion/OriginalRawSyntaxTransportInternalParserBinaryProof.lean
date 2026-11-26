module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParserSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every tag-two/seven raw input reconstructs its metadata and two ordered
children. This is the reverse parser direction, without a constructor premise. -/
theorem binaryCases (tag : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral tag) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (metadata first second : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph3 (pairOf (constant 3 tag)
          (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2))))
          (raw.relabel j) metadata first second)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 5 → Program 1 :=
    ![InternalUnpair.right,rightOf InternalUnpair.right,leftOf InternalUnpair.right,
      leftOf (rightOf InternalUnpair.right),rightOf (rightOf InternalUnpair.right)]
  apply programsCases ps (Fin.cons raw Fin.elim0) psi
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  have ht' := OriginalRawSyntaxTransportInternalParserSyntaxProof.literalGraphRename
    rawTag tag raw ht j Theta hj
  have hp : Nonempty (Derivation body Theta
      (graph1 InternalUnpair.right (ys 0) (raw.relabel j))) := hs 0
  have hchildren := selectorPair (rightOf InternalUnpair.right) (ys 1) (ys 3) (ys 4)
    (Fin.cons (raw.relabel j) Fin.elim0) (hs 1) (hs 3) (hs 4)
  have hpair := selectorPair InternalUnpair.right (ys 0) (ys 2) (ys 1)
    (Fin.cons (raw.relabel j) Fin.elim0) hp (hs 2) (hs 1)
  exact step beta j Theta (ys 2) (ys 3) (ys 4) hj
    (binaryConstructorValue tag (raw.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
      (reconstructPair (raw.relabel j) (numeral tag) (ys 0) ht' hp) hpair hchildren)

theorem applicationCases (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 2) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (domain fn arg : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph3 applicationConstructor (raw.relabel j) domain fn arg)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  binaryCases 2 raw psi ht step

theorem consCases (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 7) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (tau head tail : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph3 consConstructor (raw.relabel j) tau head tail)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  binaryCases 7 raw psi ht step

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserBinaryProof
