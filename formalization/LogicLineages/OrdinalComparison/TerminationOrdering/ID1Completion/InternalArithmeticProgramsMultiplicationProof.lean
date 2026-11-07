module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalArithmeticPrograms
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalArithmeticProgramsSupportProof InternalControlGraphSupportProof
open InternalRecursionGraphSuccessorIntroductionProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalMultiplicationLawsProof InternalMultiplicationLeftSuccessorProof
open InternalSourceInversionSupportProof SourceComputabilityFormulaSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem multiplicationZero (y : OTerm α) : Nonempty (Derivation body Gamma (binaryGraph multiplication z z y)) := by
  apply recursionZeroValue multiplicationBase multiplicationStep z (Fin.cons y Fin.elim0)
  exact compositionValue .zero Fin.elim0 z (Fin.cons y Fin.elim0) Fin.elim0
    (zeroValue Fin.elim0) (fun i => Fin.elim0 i)

theorem multiplicationSuccessor (old x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (binaryGraph multiplication old x y))) :
    Nonempty (Derivation body Gamma (binaryGraph multiplication (add old y) (suc x) y)) := by
  apply recursionSuccessorIntroduction Gamma (OrdinaryArithmetic.graphFormula multiplicationBase)
    (OrdinaryArithmetic.graphFormula multiplicationStep) (add old y) x old (Fin.cons y Fin.elim0) h
  apply compositionValue addition
    (Fin.cons (.projection (1 : Fin 3)) (Fin.cons (.projection (2 : Fin 3)) Fin.elim0))
    (add old y) (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0))) (Fin.cons old (Fin.cons y Fin.elim0))
    (additionValue old y)
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · exact projectionValue (1 : Fin 3) (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0)))
  · exact projectionValue (2 : Fin 3) (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0)))

/-- Actual PA induction and the original recursive graph successor equation. -/
theorem multiplicationValue (x y : OTerm α) :
    Nonempty (Derivation body Gamma (binaryGraph multiplication (mul x y) x y)) := by
  let a := y.relabel (Sum.inl : α → α ⊕ Fin 1)
  let v : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta := binaryGraph multiplication (mul v a) v a
  have hb : Derivation body Gamma (instantiate theta (emb z)) := by
    simp only [theta,a,v,binaryGraphInstantiate,mulSubst,varBind,liftBind]
    exact Classical.choice (outputTransport multiplication z (mul z y) (Fin.cons z (Fin.cons y Fin.elim0))
      ⟨symm (multiplicationLeftZero y)⟩ (multiplicationZero y))
  have hs : Derivation body (theta :: Gamma.map weaken) (successorInstance theta) := by
    simp only [theta,a,v,successorInstance,nextEmbedding,binaryGraphSubst,mulSubst,varNext,liftNext]
    have prev : Nonempty (Derivation body (theta :: Gamma.map weaken) (binaryGraph multiplication (mul v a) v a)) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    exact Classical.choice (outputTransport multiplication (add (mul v a) a) (mul (suc v) a)
      (Fin.cons (suc v) (Fin.cons a Fin.elim0)) ⟨symm (leftSuccessorMultiplication v a)⟩
      (multiplicationSuccessor (mul v a) v a prev))
  have h := Derivation.universalElimination (emb x) (natInduction theta hb hs)
  simpa only [theta,a,v,binaryGraphInstantiate,mulSubst,varBind,liftBind] using (Nonempty.intro h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof
