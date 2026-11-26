module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineQueriesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def targetMark (measure : Program 1) : Program 3 :=
  .composition measure (fun _ : Fin 1 => rightOf (.projection 2))

/-- Inputs are [context,sourceObject,targetObject]. Every coordinate,
runtime pair and target mark/depth is bound by original Program totality. -/
def queries (measure : Program 1) : Fin 6 → Program 3 :=
  Fin.cons (leftOf (.projection 1)) (Fin.cons (rightOf (.projection 1))
    (Fin.cons (rightOf (.projection 2))
      (Fin.cons (pairOf (.projection 0) (leftOf (.projection 1)))
        (Fin.cons (targetMark measure) (Fin.cons (rightOf (targetMark measure)) Fin.elim0)))))

theorem coordinateCases {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}
    (measure : Program 1) (context f g : OTerm α) (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (gammaCode fp gp parameter mark depth : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.left gammaCode (f.relabel j))) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp (f.relabel j))) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right gp (g.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 InternalPairing.pairing parameter (context.relabel j) gammaCode)) →
      Nonempty (Derivation body Delta (graph1 measure mark gp)) →
      Nonempty (Derivation body Delta (graph1 InternalUnpair.right depth mark)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  apply queryCases (queries measure) (Fin.cons context (Fin.cons f (Fin.cons g Fin.elim0))) psi
  intro β j ys Delta hj hq
  simp only [consTermRename,emptyRename] at hq
  let xs : Fin 3 → OTerm β :=
    Fin.cons (context.relabel j) (Fin.cons (f.relabel j) (Fin.cons (g.relabel j) Fin.elim0))
  have hgamma := unaryRecover InternalUnpair.left (.projection (1 : Fin 3))
    (ys 0) (f.relabel j) xs (hq 0) (projectionValue 1 xs)
  have hfp := unaryRecover InternalUnpair.right (.projection (1 : Fin 3))
    (ys 1) (f.relabel j) xs (hq 1) (projectionValue 1 xs)
  have hgp := unaryRecover InternalUnpair.right (.projection (2 : Fin 3))
    (ys 2) (g.relabel j) xs (hq 2) (projectionValue 2 xs)
  have hparameter := binaryRecover InternalPairing.pairing (.projection (0 : Fin 3))
    (leftOf (.projection 1)) (ys 3) (context.relabel j) (ys 0) xs
    (hq 3) (projectionValue 0 xs) (hq 0)
  have hmark := unaryRecover measure (rightOf (.projection (2 : Fin 3)))
    (ys 4) (ys 2) xs (hq 4) (hq 2)
  have hdepth := unaryRecover InternalUnpair.right (targetMark measure)
    (ys 5) (ys 4) xs (hq 5) (hq 4)
  exact h β j Delta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    hj hgamma hfp hgp hparameter hmark hdepth

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineQueriesProof
