module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorInductionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsChildQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorErasureSyntax EvaluatorConstructorInductionDefinitions
open EvaluatorConstructorInductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
theorem actualCases (d cutoff : OTerm alpha) (children : Fin 4 → OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (outs : Fin 4 → OTerm beta),
  (∀ q ∈ Delta, q.relabel j ∈ Theta) →
  (∀ i : Fin 4, Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw
    (outs i) (d.relabel j) (cutoff.relabel j) ((children i).relabel j)))) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let qs : Fin 4 → Program 6 := fun i => .composition OriginalRawSyntaxTransport.erasePackedRaw
   ![.projection 0,.projection 1,.projection ⟨i.val+2,by omega⟩]
 let args : Fin 6 → OTerm alpha := Fin.cons d (Fin.cons cutoff children)
 apply programsCases qs args psi
 intro beta j Theta outs hj hq
 let xs : Fin 6 → OTerm beta := fun i => (args i).relabel j
 apply next beta j Theta outs hj
 intro i
 have he := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) (.projection 1)
  (.projection ⟨i.val+2,by omega⟩) (outs i) (xs 0) (xs 1) (xs ⟨i.val+2,by omega⟩) xs
  (hq i) (projectionValue 0 xs) (projectionValue 1 xs) (projectionValue ⟨i.val+2,by omega⟩ xs)
 have index : (⟨i.val+2,by omega⟩ : Fin 6) = i.succ.succ := by
  apply Fin.ext
  rfl
 rw [index] at he
 have hone : (1 : Fin 6) = (0 : Fin 5).succ := rfl
 simpa only [xs,args,hone,Fin.cons_zero,Fin.cons_succ] using he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsChildQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorApplicationCellsChildQueries
