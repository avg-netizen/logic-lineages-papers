module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenRowProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc)
open ID1Completion.InternalRawListRecursionSupportProof (recursionRecover)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue)
open ID1Completion.InternalUnpair (left right)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalCoverGrammarStageTargets (initialLayer termsBefore argsBefore)
open NumberedWindowInternalCoverAscendingRangeTargets (ascendingRange rangeReport)
open NumberedWindowInternalCoverNamedLeavesTargets (idsAt boundSuccessor)
open NumberedWindowInternalCoverSelectedSuccessorTargets (stepTape stepReport selectedStep termProjection argsProjection)
open NumberedWindowInternalCoverSelectedGrammarTargets
open NumberedWindowInternalCoverSelectedGrammarOpenTargets

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem alignStageTape (d H K M : OTerm α) :
    grammarTape d H K M = Fin.cons d ![H,K,M] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i

private theorem rowAlignment (d prev H K M : OTerm α) :
    (Fin.cons d (Fin.cons prev ![H,K,M]) : Fin 5 → OTerm α) = rowTape d prev H K M := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun k => Fin.elim0 k))))) i

private theorem priorField (p : Program 1) (x d prev H K M : OTerm α)
    (known : Nonempty (Derivation body Γ (unary p x prev))) :
    Nonempty (Derivation body Γ (programGraph (reorder p ![1]) x (rowTape d prev H K M))) := by
  let xs := rowTape d prev H K M
  apply compositionValue p (fun i => .projection ((![1] : Fin 1 → Fin 5) i))
    x xs ![prev] known
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 1 xs

private theorem actualIds (K M ids : OTerm α)
    (run : Nonempty (Derivation body Γ (rangeReport ids (suc M)))) :
    Nonempty (Derivation body Γ (programGraph idsAt ids ![K,M])) := by
  let xs : Fin 2 → OTerm α := ![K,M]
  have next : Nonempty (Derivation body Γ (programGraph boundSuccessor (suc M) xs)) := by
    apply compositionValue (.succ : Program 1) (fun _ : Fin 1 => .projection 1)
      (suc M) xs ![M] (successorValue ![M])
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 1 xs
  apply compositionValue ascendingRange (fun _ : Fin 1 => boundSuccessor) ids xs ![suc M] run
  intro i
  obtain rfl := Fin.eq_zero i
  exact next

private theorem rowIds (d prev H K M ids : OTerm α)
    (range : Nonempty (Derivation body Γ (rangeReport ids (suc M)))) :
    Nonempty (Derivation body Γ (programGraph selectedIds ids (rowTape d prev H K M))) := by
  let xs := rowTape d prev H K M
  apply compositionValue idsAt (fun i => .projection ((![3,4] : Fin 2 → Fin 5) i))
    ids xs ![K,M] (actualIds K M ids range)
  intro i
  exact Fin.cases (projectionValue 3 xs) (Fin.cases (projectionValue 4 xs) (fun j => Fin.elim0 j)) i

theorem exact_OpenSelectedGrammarSuccessorRow : ExactOpenSelectedGrammarSuccessorRow := by
  intro body α Γ prev next d H K M ids terms args old new tRead aRead range
  let params : Fin 3 → OTerm α := ![H,K,M]
  rw [grammarReport,alignStageTape] at old new
  have row := recursionRecover initialLayer selectedGrammarRow next prev d params old new
  rw [rowAlignment] at row
  let xs := rowTape d prev H K M
  have t := priorField left terms d prev H K M tRead
  have a := priorField right args d prev H K M aRead
  have i := rowIds d prev H K M ids range
  apply compositionRecover selectedStep selectedRowInputs next xs (stepTape H K ids terms args) row
  intro n
  exact Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs)
    (Fin.cases i (Fin.cases t (Fin.cases a (fun q => Fin.elim0 q))))) n

#print axioms exact_OpenSelectedGrammarSuccessorRow

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOpenRowProof
