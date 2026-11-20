module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgsRename loopArgs)
open NumberedWindowInternalSparsePositiveIterationBindingProof (loopArgsSubst)

attribute [local irreducible] programGraph

theorem oneRename {α β : Type} (n : OTerm α) (j : α → β) :
    (fun i => ((![n] : Fin 1 → OTerm α) i).relabel j) = ![n.relabel j] := by
  funext i
  obtain rfl := Fin.eq_zero i
  rfl

theorem unarySubst {α β : Type} (p : Program 1) (out n : OTerm α) (ts : α → OTerm β) :
    (unary p out n).subst (fun a => emb (ts a)) = unary p (out.subst ts) (n.subst ts) := by
  have h : (fun i => ((![n] : Fin 1 → OTerm α) i).subst ts) = ![n.subst ts] := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  unfold unary
  rw [programSubst,h]

theorem graph3Rename {α β : Type} (p : Program 3) (out x y w : OTerm α) (j : α → β) :
    (programGraph p out ![x,y,w]).relabel j =
      programGraph p (out.relabel j) ![x.relabel j,y.relabel j,w.relabel j] := by
  rw [programRename,tripleInputsRename]

theorem graph5Rename {α β : Type} (p : Program 5) (out a b c d e : OTerm α) (j : α → β) :
    (programGraph p out ![a,b,c,d,e]).relabel j =
      programGraph p (out.relabel j) ![a.relabel j,b.relabel j,c.relabel j,d.relabel j,e.relabel j] := by
  change (programGraph p out (loopArgs a b c d e)).relabel j = _
  rw [programRename,loopArgsRename] <;> rfl

theorem graph3Subst {α β : Type} (p : Program 3) (out x y w : OTerm α) (ts : α → OTerm β) :
    (programGraph p out ![x,y,w]).subst (fun a => emb (ts a)) =
      programGraph p (out.subst ts) ![x.subst ts,y.subst ts,w.subst ts] := by
  have h : (fun i => ((![x,y,w] : Fin 3 → OTerm α) i).subst ts) = ![x.subst ts,y.subst ts,w.subst ts] := by
    funext i
    refine Fin.cases ?_ (fun x => Fin.cases ?_ (fun y => Fin.cases ?_ (fun z => Fin.elim0 z) y) x) i <;> rfl
  rw [programSubst,h]

theorem graph5Subst {α β : Type} (p : Program 5) (out a b c d e : OTerm α) (ts : α → OTerm β) :
    (programGraph p out ![a,b,c,d,e]).subst (fun x => emb (ts x)) =
      programGraph p (out.subst ts) ![a.subst ts,b.subst ts,c.subst ts,d.subst ts,e.subst ts] := by
  change (programGraph p out (loopArgs a b c d e)).subst (fun x => emb (ts x)) = _
  rw [programSubst,loopArgsSubst] <;> rfl

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
