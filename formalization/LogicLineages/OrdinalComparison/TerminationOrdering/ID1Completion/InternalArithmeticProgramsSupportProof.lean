module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalMultiplicationLeftSuccessorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalArithmeticPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalControlGraphSupportProof InternalGraphCompositionSyntaxProof
open InternalRecursionGraphSuccessorIntroductionProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalSourceInversionSupportProof SourceComputabilityFormulaSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

abbrev binaryGraph (p : Program 2) (out x y : OTerm α) : Formula α :=
  programGraph p out (Fin.cons x (Fin.cons y Fin.elim0))

@[simp] theorem binaryGraphSubst {β : Type} (p : Program 2) (out x y : OTerm α) (ts : α → OTerm β) :
    (binaryGraph p out x y).subst (fun a => emb (ts a)) =
      binaryGraph p (out.subst ts) (x.subst ts) (y.subst ts) := by
  unfold binaryGraph programGraph
  rw [graphSubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> rfl

@[simp] theorem binaryGraphInstantiate (p : Program 2) (out x y : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (binaryGraph p out x y) (emb t) =
      binaryGraph p (out.subst (bindTerm t)) (x.subst (bindTerm t)) (y.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,binaryGraphSubst]

theorem additionZero (y : OTerm α) : Nonempty (Derivation body Gamma (binaryGraph addition y z y)) :=
  recursionZeroValue (.projection (0 : Fin 1)) additionStep y (Fin.cons y Fin.elim0)
    (projectionValue (0 : Fin 1) (Fin.cons y Fin.elim0))

theorem additionSuccessor (old x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (binaryGraph addition old x y))) :
    Nonempty (Derivation body Gamma (binaryGraph addition (suc old) (suc x) y)) := by
  apply recursionSuccessorIntroduction Gamma (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1)))
    (OrdinaryArithmetic.graphFormula additionStep) (suc old) x old (Fin.cons y Fin.elim0) h
  apply compositionValue .succ (fun _ : Fin 1 => .projection (1 : Fin 3)) (suc old)
    (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0))) (Fin.cons old Fin.elim0)
    (successorValue (Fin.cons old Fin.elim0))
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact projectionValue (1 : Fin 3) (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0)))

/-- The induction variable is the original first input. The fixed second
input is an arbitrary term with all original free parameters preserved. -/
theorem additionValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph addition (add x y) x y)) := by
  let a := y.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := binaryGraph addition (add v a) v a
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,v,binaryGraphInstantiate,addSubst,varBind,liftBind]
    exact Classical.choice (outputTransport addition y (add z y) (Fin.cons z (Fin.cons y Fin.elim0))
      ⟨symm (leftZero y)⟩ (additionZero y))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,v,successorInstance,nextEmbedding,binaryGraphSubst,addSubst,varNext,liftNext]
    have prev : Nonempty (Derivation body (theta :: Gamma.map weaken) (binaryGraph addition (add v a) v a)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact Classical.choice (outputTransport addition (suc (add v a)) (add (suc v) a)
      (Fin.cons (suc v) (Fin.cons a Fin.elim0)) ⟨symm (leftSuccessor v a)⟩
      (additionSuccessor (add v a) v a prev))
  have h := Derivation.universalElimination (emb x) (natInduction theta hb hs)
  simpa only [theta,a,v,binaryGraphInstantiate,addSubst,varBind,liftBind] using (Nonempty.intro h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
