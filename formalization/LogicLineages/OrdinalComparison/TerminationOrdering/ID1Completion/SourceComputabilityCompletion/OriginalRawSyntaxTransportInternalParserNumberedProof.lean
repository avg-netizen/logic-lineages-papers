module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedValueProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalParserSupportProof
open OriginalRawSyntaxTransportInternalParserNumberedValueProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Reconstruct every tag-five arithmetic input. All metadata, both recursive
children and the five intermediate pair payloads are existentially bound inside
the original calculus. In particular no type-list decoding is required. -/
theorem numberedCases (raw : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 rawTag (numeral 5) raw)))
    (step : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (label head tau base types extras : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (programGraph numberedConstructor (raw.relabel j) ![label,head,tau,base,types,extras])) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let r1 : Program 1 := InternalUnpair.right
  let r2 : Program 1 := rightOf r1
  let r3 : Program 1 := rightOf r2
  let r4 : Program 1 := rightOf r3
  let r5 : Program 1 := rightOf r4
  let ps : Fin 11 → Program 1 :=
    ![r1,r2,r3,r4,r5,leftOf r1,leftOf r2,leftOf r3,leftOf r4,leftOf r5,rightOf r5]
  apply programsCases ps (Fin.cons raw Fin.elim0) psi
  intro beta j Theta ys hj hs
  simp only [consTermRename,emptyRename] at hs
  have ht' := OriginalRawSyntaxTransportInternalParserSyntaxProof.literalGraphRename
    rawTag 5 raw ht j Theta hj
  let xs : Fin 1 → OTerm beta := Fin.cons (raw.relabel j) Fin.elim0
  have hp : Nonempty (Derivation body Theta
      (graph1 InternalUnpair.right (ys 0) (raw.relabel j))) := hs 0
  have h1 := selectorPair r1 (ys 0) (ys 5) (ys 1) xs (hs 0) (hs 5) (hs 1)
  have h2 := selectorPair r2 (ys 1) (ys 6) (ys 2) xs (hs 1) (hs 6) (hs 2)
  have h3 := selectorPair r3 (ys 2) (ys 7) (ys 3) xs (hs 2) (hs 7) (hs 3)
  have h4 := selectorPair r4 (ys 3) (ys 8) (ys 4) xs (hs 3) (hs 8) (hs 4)
  have h5 := selectorPair r5 (ys 4) (ys 9) (ys 10) xs (hs 4) (hs 9) (hs 10)
  exact step beta j Theta (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) hj
    (numberedConstructorValue (raw.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
      (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10)
      (reconstructPair (raw.relabel j) (numeral 5) (ys 0) ht' hp) h1 h2 h3 h4 h5)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
