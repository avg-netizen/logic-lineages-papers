module
public import LogicLineages.PersistentMarking.NumberedWindowPositiveFiberOpenTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalDerivationRenamingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowPositiveFiberSharedSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel)
open ID1Completion.InternalGraphCompositionSyntaxProof (graphOutputInstantiate)
open ID1Completion.InternalDerivationRenamingSyntaxProof (existsRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalRecursionClosureSyntaxProof (conjunctionSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowPositiveFiberOpenTargets

theorem tupleRename {α β : Type} (q w v : OTerm α) (j : α → β) :
    (fun i : Fin 3 => (![q,w,v] i).relabel j) = ![q.relabel j,w.relabel j,v.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i

theorem oneRename {α β : Type} (r : Program 3) (q w v : OTerm α) (j : α → β) :
    (one r q w v).relabel j = one r (q.relabel j) (w.relabel j) (v.relabel j) := by
  simp only [one,programRename,zRelabel,sucRelabel,tupleRename]

private theorem unaryRename {α β : Type} (a : Program 1) (n q : OTerm α) (j : α → β) :
    (programGraph a n ![q]).relabel j = programGraph a (n.relabel j) ![q.relabel j] := by
  rw [programRename]
  congr 1
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem sharedRename {α β : Type} (a : Program 1) (q v : OTerm α) (j : α → β) :
    (shared a q v).relabel j = shared a (q.relabel j) (v.relabel j) := by
  simp only [shared,existsRename,conjunctionRename,unaryRename,Term.relabel_relabel]
  rfl

private theorem unaryInstantiate {α : Type} (a : Program 1) (n q : OTerm α) :
    instantiate (programGraph a (.var (.inr 0)) ![q.relabel Sum.inl]) (emb n) =
      programGraph a n ![q] := by
  have arg : (fun i : Fin 1 => (![q] i).relabel Sum.inl) = ![q.relabel Sum.inl] := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  rw [← arg]
  exact graphOutputInstantiate _ n ![q]

theorem sharedIntro {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (a : Program 1) (q v n : OTerm α)
    (hq : Nonempty (Derivation body Γ (programGraph a n ![q])))
    (hv : Nonempty (Derivation body Γ (programGraph a n ![v]))) :
    Nonempty (Derivation body Γ (shared a q v)) := by
  obtain ⟨hq⟩ := hq
  obtain ⟨hv⟩ := hv
  apply Nonempty.intro
  unfold shared
  apply Derivation.existentialIntroduction (emb n)
  change Derivation body Γ (instantiate
    (programGraph a (.var (.inr 0)) ![q.relabel Sum.inl] ⊓
      programGraph a (.var (.inr 0)) ![v.relabel Sum.inl]) (emb n))
  have conj {p r : Formula (α ⊕ Fin 1)} :
      instantiate (p ⊓ r) (emb n) = (instantiate p (emb n) ⊓ instantiate r (emb n)) :=
    conjunctionSubst p r _
  rw [conj,unaryInstantiate,unaryInstantiate]
  exact Derivation.conjunctionIntroduction hq hv

end LogicLineages.PersistentMarking.NumberedWindowPositiveFiberSharedSyntaxProof
