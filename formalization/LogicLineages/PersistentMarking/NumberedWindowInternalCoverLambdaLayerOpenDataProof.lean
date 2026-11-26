module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxApplicationsOpenDataProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerOpenDataProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open NumberedWindowInternalCoverCartesianFoldTargets (flatMap flatGraph)
open NumberedWindowInternalCoverAuxApplicationsOpenDataProof (recoverReordered)
open NumberedWindowInternalCoverNamedLeavesTargets (singletonLeaf typeBlock)
open NumberedWindowInternalCoverLambdaLayerTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem outerGraph (out K children : OTerm α)
    (actual : Nonempty (Derivation body Γ (lambdaReport out K children))) :
    Nonempty (Derivation body Γ (flatGraph (typeBlock 2) out K ![children])) := by
  have h : Nonempty (Derivation body Γ (programGraph (flatMap (typeBlock 2)) out ![K,children])) := actual
  have tape : (![K,children] : Fin 2 → OTerm α) = Fin.cons K ![children] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at h
  exact h

theorem innerGraph (out ty children : OTerm α)
    (actual : Nonempty (Derivation body Γ (programGraph (typeBlock 2) out ![ty,children]))) :
    Nonempty (Derivation body Γ (flatGraph (singletonLeaf 2) out children ![ty])) := by
  have recovered := recoverReordered (flatMap (singletonLeaf 2))
    (![1,0] : Fin 2 → Fin 2) out ![ty,children] actual
  have tape : (fun i => (![ty,children] : Fin 2 → OTerm α) ((![1,0] : Fin 2 → Fin 2) i)) =
      Fin.cons children ![ty] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j)) i
  rw [tape] at recovered
  exact recovered

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverLambdaLayerOpenDataProof
