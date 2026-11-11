module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParserSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every payload is itself a pair, including arbitrary raw arithmetic inputs.
The metadata and child are supplied by internal totality, not assumed externally. -/
theorem unaryCases (tag : Nat) (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral tag) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (metadata child : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 (pairOf (constant 2 tag) (pairOf (.projection 0) (.projection 1)))
          (raw.relabel j) metadata child)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let ps : Fin 3 → Program 1 :=
    ![InternalUnpair.right,leftOf InternalUnpair.right,rightOf InternalUnpair.right]
  apply programsCases ps (Fin.cons raw Fin.elim0) psi
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  have ht' := OriginalRawSyntaxTransportInternalParserSyntaxProof.literalGraphRename
    rawTag tag raw ht j Theta hj
  have hp : Nonempty (Derivation body Theta
      (graph1 InternalUnpair.right (ys 0) (raw.relabel j))) := hs 0
  have hpair := selectorPair InternalUnpair.right (ys 0) (ys 1) (ys 2)
    (Fin.cons (raw.relabel j) Fin.elim0) hp (hs 1) (hs 2)
  exact step beta j Theta (ys 1) (ys 2) hj
    (unaryConstructorValue tag (raw.relabel j) (ys 0) (ys 1) (ys 2)
      (reconstructPair (raw.relabel j) (numeral tag) (ys 0) ht' hp) hpair)

theorem lambdaCases (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 1) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (domain child : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 lambdaConstructor (raw.relabel j) domain child)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  unaryCases 1 raw psi ht step

theorem ordinaryCases (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 4) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (head base : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 ordinaryConstructor (raw.relabel j) head base)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) :=
  unaryCases 4 raw psi ht step

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
