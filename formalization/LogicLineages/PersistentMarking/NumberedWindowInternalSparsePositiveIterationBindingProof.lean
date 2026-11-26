module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationSuccessorProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionClosureSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalRawListRecursionSyntaxProof (programSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePositiveFold (iterateState)
open NumberedWindowInternalSparsePositiveFoldTargets (scratchGraph loopGraph)
open NumberedWindowInternalSparsePositiveFoldOpenSyntaxProof (call6)
open NumberedWindowInternalSparsePositiveIterationSuccessorProof (loopArgs)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)

theorem loopArgsSubst {α β : Type} (fuel c ty start cert : OTerm α) (ts : α → OTerm β) :
    (fun i => (loopArgs fuel c ty start cert i).subst ts) =
      loopArgs (fuel.subst ts) (c.subst ts) (ty.subst ts) (start.subst ts) (cert.subst ts) := by
  funext i
  refine Fin.cases ?_ (fun a => Fin.cases ?_ (fun b => Fin.cases ?_ (fun d =>
    Fin.cases ?_ (fun e => Fin.cases ?_ (fun u => Fin.elim0 u) e) d) b) a) i <;> rfl

theorem loopSubst {α β : Type} (raw : Program 5) (least : Program 3)
    (out fuel c ty start cert : OTerm α) (ts : α → OTerm β) :
    (loopGraph raw least out fuel c ty start cert).subst (fun a => emb (ts a)) =
      loopGraph raw least (out.subst ts) (fuel.subst ts) (c.subst ts) (ty.subst ts)
        (start.subst ts) (cert.subst ts) := by
  unfold loopGraph
  change (programGraph (iterateState raw least) out (loopArgs fuel c ty start cert)).subst
    (fun a => emb (ts a)) = _
  rw [programSubst,loopArgsSubst] <;> rfl

theorem scratchRename {α β : Type} (o c s : OTerm α) (j : α → β) :
    (scratchGraph o c s).relabel j = scratchGraph (o.relabel j) (c.relabel j) (s.relabel j) := by
  simp only [scratchGraph,programRename,binaryInputsRename]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationBindingProof
