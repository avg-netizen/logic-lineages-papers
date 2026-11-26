module
public import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphSubst)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb z sucRelabel zRelabel bindEmbedding bindTerm sucSubst liftBind varBind)
open NumberedWindowInternalProbeTargets (OTerm freshAt)
open NumberedWindowInternalFreshProbeTargets (rejectedAt chosenAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem unaryRename {α β : Type} (q : OTerm α) (j : α → β) :
    (fun i : Fin 1 => (![q] i).relabel j) = ![q.relabel j] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem unarySubst {α β : Type} (q : OTerm α) (s : α → OTerm β) :
    (fun i : Fin 1 => (![q] i).subst s) = ![q.subst s] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem freshRename {α β : Type} (a : Program 1) (q u : OTerm α) (j : α → β) :
    (freshAt a q u).relabel j = freshAt a (q.relabel j) (u.relabel j) := by
  simp only [freshAt,programRename,sucRelabel,unaryRename]

theorem rejectedRename {α β : Type} (a : Program 1) (q : OTerm α) (j : α → β) :
    (rejectedAt a q).relabel j = rejectedAt a (q.relabel j) := by
  simp only [rejectedAt,programRename,zRelabel,unaryRename]

theorem chosenRename {α β : Type} (a : Program 1) (q : OTerm α) (j : α → β) :
    (chosenAt a q).relabel j = chosenAt a (q.relabel j) := by
  simp only [chosenAt,existsRename,freshRename,Term.relabel_relabel] <;> rfl

theorem splitRename {α β : Type} (a : Program 1) (q : OTerm α) (j : α → β) :
    (rejectedAt a q ⊔ chosenAt a q).relabel j =
      rejectedAt a (q.relabel j) ⊔ chosenAt a (q.relabel j) := by
  change (((rejectedAt a q).relabel j).not.imp ((chosenAt a q).relabel j)) = _
  rw [rejectedRename,chosenRename] <;> rfl

theorem freshSubst {α β : Type} (a : Program 1) (q u : OTerm α) (s : α → OTerm β) :
    (freshAt a q u).subst (fun i => emb (s i)) = freshAt a (q.subst s) (u.subst s) := by
  simp only [freshAt,programGraph,graphSubst,sucSubst,unarySubst]

theorem freshInstantiate {α : Type} (a : Program 1) (q u : OTerm α) :
    instantiate (freshAt a (q.relabel Sum.inl) (.var (.inr (0 : Fin 1)))) (emb u) =
      freshAt a q u := by
  rw [instantiate,bindEmbedding,freshSubst,liftBind,varBind]

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeSyntaxProof
