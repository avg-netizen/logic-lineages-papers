module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputQueriesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputCasesProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationStepPeel (graph5)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalFiniteBlocksBindingProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

/-- Simultaneously bind exactly the original coordinates and both actual
raw vertex outputs used by the full source lift. All seven witnesses come
from original Program totality, before any mathematical source premise. -/
theorem inputCases (data : Data) (window : Program 1) (oldVertex : Program 5)
    (context : Nat) (sigma tau : Ty) (f g a : OTerm α) (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β)
      (gammaCode x y argument parameter out other : OTerm β) (Theta : List (Formula β)),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.left gammaCode (f.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right x (f.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right y (g.relabel j))) →
      Nonempty (Derivation body Theta (graph1 InternalUnpair.right argument (a.relabel j))) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing parameter (SourceComputabilityFormulaSupportProof.numeral context) gammaCode)) →
      Nonempty (Derivation body Theta
        (graph5 (Path.vertex data window oldVertex) out parameter
          (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber sigma))
          (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber tau)) argument x)) →
      Nonempty (Derivation body Theta
        (graph5 (Path.vertex data window oldVertex) other parameter
          (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber sigma))
          (SourceComputabilityFormulaSupportProof.numeral (NumberedLeastCodeRepresentative.typeNumber tau)) argument y)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply queryCases (OuterInputQueries.queries data window oldVertex context sigma tau)
    (Fin.cons f (Fin.cons g (Fin.cons a Fin.elim0))) psi
  intro β j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 3 → OTerm β :=
    Fin.cons (f.relabel j) (Fin.cons (g.relabel j) (Fin.cons (a.relabel j) Fin.elim0))
  have hg := unaryRecover InternalUnpair.left (.projection (0 : Fin 3)) (ys 0)
    (f.relabel j) xs (hq 0) (projectionValue 0 xs)
  have hx := unaryRecover InternalUnpair.right (.projection (0 : Fin 3)) (ys 1)
    (f.relabel j) xs (hq 1) (projectionValue 0 xs)
  have hy := unaryRecover InternalUnpair.right (.projection (1 : Fin 3)) (ys 2)
    (g.relabel j) xs (hq 2) (projectionValue 1 xs)
  have ha := unaryRecover InternalUnpair.right (.projection (2 : Fin 3)) (ys 3)
    (a.relabel j) xs (hq 3) (projectionValue 2 xs)
  have hp := OuterInputQueriesProof.parameterRecover context xs (ys 0) (ys 4) hg (hq 4)
  have ho := OuterInputQueriesProof.rawVertexRecover data window oldVertex context sigma tau
    0 xs (ys 4) (ys 3) (ys 1) (ys 5) (hq 4) ha hx (hq 5)
  have hv := OuterInputQueriesProof.rawVertexRecover data window oldVertex context sigma tau
    1 xs (ys 4) (ys 3) (ys 2) (ys 6) (hq 4) ha hy (hq 6)
  exact h β j (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) Theta hj hg hx hy ha hp ho hv

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.OuterInputCasesProof
