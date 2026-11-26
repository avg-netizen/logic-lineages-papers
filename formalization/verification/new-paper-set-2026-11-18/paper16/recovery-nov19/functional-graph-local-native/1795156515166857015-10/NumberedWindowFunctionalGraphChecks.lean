module
public import LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalEqualityTestEvaluationProof (vectorOne vectorTwo exactEqualityEvaluation)
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl symm cancelSuc)
open ID1Completion.InternalControlGraphSupportProof
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCases)
open ID1Completion.InternalEqualityTestCompositionProof (equalityOfAcceptance equalityOfEqual)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowFunctionalGraphTargets NumberedWindowComputabilityFormulaTargets

theorem exact_Evaluation : Evaluation := by
  intro a f u v
  simp only [graphProgram,evaluate,vectorTwo,Matrix.cons_val_zero,Matrix.cons_val_one,
    someValue,firstTwo,vectorOne]
  exact exactEqualityEvaluation _ _

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem firstTwoValue (a : Program 2) (f u v n : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph a n ![f,u]))) :
    Nonempty (Derivation body Γ (programGraph (firstTwo a) n ![f,u,v])) := by
  apply compositionValue a (fun i => .projection i.castSucc) n ![f,u,v] ![f,u] h
  intro i
  exact Fin.cases (projectionValue 0 ![f,u,v]) (Fin.cases (projectionValue 1 ![f,u,v]) (fun k => Fin.elim0 k)) i

private theorem someValueGraph (f u v : OTerm α) :
    Nonempty (Derivation body Γ (programGraph someValue (suc v) ![f,u,v])) := by
  apply compositionValue .succ (fun _ => .projection 2) (suc v) ![f,u,v] ![v] (successorValue ![v])
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 2 ![f,u,v]

private theorem outputRule (a : Program 2) : OutputRule a (graphProgram a) := by
  intro body α Γ f u v
  constructor
  · intro h
    apply programCases a ![f,u] _
    intro β j Δ n hj hn
    rw [programRename,sucRelabel]
    have h' := renameInto h j Δ hj
    change Nonempty (Derivation body Δ ((programGraph (graphProgram a) (suc z) ![f,u,v]).relabel j)) at h'
    rw [programRename, sucRelabel,ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at h'
    let F := f.relabel j
    let U := u.relabel j
    let V := v.relabel j
    have hxs : (fun i => (![f,u,v] i).relabel j) = ![F,U,V] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
    have hargs : (fun i => (![f,u] i).relabel j) = ![F,U] := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
    rw [hxs] at h'
    rw [hargs] at hn ⊢
    have compared := compositionRecover ID1Completion.InternalEqualityTest.equalityTest
      ![someValue,firstTwo a] (suc z) ![F,U,V] ![suc V,n] h'
      (fun i => Fin.cases (someValueGraph F U V) (Fin.cases (firstTwoValue a F U V n hn) (fun k => Fin.elim0 k)) i)
    obtain ⟨eq⟩ := equalityOfAcceptance (suc V) n compared
    exact outputTransport a n (suc V) ![F,U] ⟨symm eq⟩ hn
  · intro h
    apply compositionValue ID1Completion.InternalEqualityTest.equalityTest ![someValue,firstTwo a]
      (suc z) ![f,u,v] ![suc v,suc v] (equalityOfEqual (suc v) (suc v) ⟨refl (suc v)⟩)
    intro i
    exact Fin.cases (someValueGraph f u v) (Fin.cases (firstTwoValue a f u v (suc v) h) (fun k => Fin.elim0 k)) i

theorem exact_FunctionalGraph : FunctionalGraph := by
  intro a
  refine ⟨outputRule a, ?_⟩
  intro body α Γ f u v w hv hw
  obtain ⟨he⟩ := valueUnique a (suc v) (suc w) ![f,u]
    ((outputRule a body α Γ f u v).mp hv) ((outputRule a body α Γ f u w).mp hw)
  rw [equalEqn]
  exact ⟨cancelSuc he⟩

#print axioms exact_Evaluation
#print axioms exact_FunctionalGraph
end LogicLineages.PersistentMarking.NumberedWindowFunctionalGraphChecks
