module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardedSourceSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplication InternalGraphCompositionSyntaxProof InternalDerivationRenamingSyntaxProof
open InternalTagArithmeticSyntaxProof (emb z suc bindEmbedding varBind liftBind zSubst sucSubst zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof

theorem inputsFirst {X : Type} (xs : Fin 5 → X) (out : X) :
    (fun i : Fin 5 => inputs xs out i.castSucc) = xs := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q))))) i

theorem mapInputs {X Y : Type} (f : X → Y) (xs : Fin 5 → X) (out : X) :
    (fun i => f (inputs xs out i)) = inputs (fun i => f (xs i)) (f out) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i

theorem inputsRename {α β : Type} (xs : Fin 5 → OTerm α) (out : OTerm α) (j : α → β) :
    (fun i => (inputs xs out i).relabel j) =
      inputs (fun i => (xs i).relabel j) (out.relabel j) :=
  mapInputs (Term.relabel j) xs out

theorem applicationExistsRename {α β : Type} (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 6)
    (xs : Fin 5 → OTerm α) (j : α → β) :
    (applicationExists p xs).relabel j = applicationExists p (fun i => (xs i).relabel j) := by
  simp only [applicationExists,existsRename,InternalControlGraphSupportProof.programRename,
    sucRelabel,zRelabel,inputsRename,Term.relabel,Term.relabel_relabel] <;> rfl

theorem applicationOutputInstantiate {α : Type}
    (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 6)
    (xs : Fin 5 → OTerm α) (out : OTerm α) :
    instantiate (programGraph p (suc z)
      (inputs (fun i => (xs i).relabel Sum.inl) (.var (.inr (0 : Fin 1))))) (emb out) =
    programGraph p (suc z) (inputs xs out) := by
  rw [instantiate,bindEmbedding]
  unfold programGraph
  rw [graphSubst]
  simp only [sucSubst,zSubst]
  congr 1
  funext i
  exact Fin.cases (liftBind (xs 0) out) (Fin.cases (liftBind (xs 1) out)
    (Fin.cases (liftBind (xs 2) out) (Fin.cases (liftBind (xs 3) out)
      (Fin.cases (liftBind (xs 4) out) (Fin.cases (varBind out 0) (fun q => Fin.elim0 q)))))) i

theorem literalApplicationGraph {α : Type}
    (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 6)
    (context : Nat) (sigma tau : Source.Ty) (f a out : OTerm α) :
    literalApplication p context sigma tau f a out = programGraph p (suc z)
      ![numeral context,numeral (NumberedLeastCodeRepresentative.typeNumber sigma),
        numeral (NumberedLeastCodeRepresentative.typeNumber tau),f,a,out] := by
  unfold literalApplication JointGammaApplication.applicationFormula
  rw [applyGraphSubst]
  unfold programGraph graph
  congr 1
  congr 1
  · simp only [sucSubst,zSubst]
  · funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)))))) i

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationSyntaxProof
