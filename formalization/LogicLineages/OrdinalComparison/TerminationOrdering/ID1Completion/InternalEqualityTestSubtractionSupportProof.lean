module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph InternalEqualityTest
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalEqualityTestPredecessorProof InternalControlGraphSupportProof
open InternalGraphCompositionEqualityProof InternalGraphCompositionSyntaxProof
open InternalRecursionGraphSuccessorIntroductionProof InternalRecursionGraphSyntaxProof
open InternalRecursionGraphStepSyntaxProof InternalRecursionClosureSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalAdditionLawsProof
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open SourceComputabilityFormulaSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

abbrev subGraph (out x y : OTerm α) : Formula α :=
  programGraph subtract out (Fin.cons x (Fin.cons y Fin.elim0))

@[simp] theorem subGraphSubst {β : Type} (out x y : OTerm α) (ts : α → OTerm β) :
    (subGraph out x y).subst (fun a => emb (ts a)) =
      subGraph (out.subst ts) (x.subst ts) (y.subst ts) := by
  unfold subGraph programGraph
  rw [graphSubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i <;> rfl

@[simp] theorem subGraphInstantiate (out x y : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (subGraph out x y) (emb t) =
      subGraph (out.subst (bindTerm t)) (x.subst (bindTerm t)) (y.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,subGraphSubst]

@[simp] theorem subGraphRename {β : Type} (out x y : OTerm α) (j : α → β) :
    (subGraph out x y).relabel j = subGraph (out.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [subGraph,programRename,consTermRename,emptyRename]

theorem subTransport (out x y x' y' : OTerm α)
    (hx : Nonempty (Derivation body Gamma (eqn x x')))
    (hy : Nonempty (Derivation body Gamma (eqn y y')))
    (h : Nonempty (Derivation body Gamma (subGraph out x y))) :
    Nonempty (Derivation body Gamma (subGraph out x' y')) := by
  apply graphInputTransport body α 2 Gamma _ out (Fin.cons x (Fin.cons y Fin.elim0))
    (Fin.cons x' (Fin.cons y' Fin.elim0)) _ h
  intro i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => Fin.elim0 k) j) i
  · rw [onEquality]
    exact hx
  · rw [onEquality]
    exact hy

theorem subtractZero (y : OTerm α) : Nonempty (Derivation body Gamma (subGraph y z y)) :=
  recursionZeroValue (.projection (0 : Fin 1)) subtractStep y (Fin.cons y Fin.elim0)
    (projectionValue (0 : Fin 1) (Fin.cons y Fin.elim0))

theorem subtractSuccessor (out old x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (subGraph old x y)))
    (hp : Nonempty (Derivation body Gamma (programGraph predecessor out (Fin.cons old Fin.elim0)))) :
    Nonempty (Derivation body Gamma (subGraph out (suc x) y)) := by
  apply recursionSuccessorIntroduction Gamma (OrdinaryArithmetic.graphFormula (.projection (0 : Fin 1)))
    (OrdinaryArithmetic.graphFormula subtractStep) out x old (Fin.cons y Fin.elim0) h
  apply compositionValue predecessor (fun _ : Fin 1 => .projection (1 : Fin 3)) out
    (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0))) (Fin.cons old Fin.elim0) hp
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact projectionValue (1 : Fin 3) (Fin.cons x (Fin.cons old (Fin.cons y Fin.elim0)))

def diagonalRow (x : OTerm α) : Formula α :=
  allOne (subGraph (.var (.inr 0)) (x.relabel Sum.inl)
    (add (x.relabel Sum.inl) (.var (.inr 0))))

@[simp] theorem diagonalRowSubst {β : Type} (x : OTerm α) (ts : α → OTerm β) :
    (diagonalRow x).subst (fun a => emb (ts a)) = diagonalRow (x.subst ts) := by
  rw [diagonalRow,actualUniversalSubstitution,liftedEmbedding,subGraphSubst]
  simp only [Term.subst,Sum.elim_inr,liftSubst,addSubst]
  rfl

@[simp] theorem diagonalRowInstantiate (x : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (diagonalRow x) (emb t) = diagonalRow (x.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,diagonalRowSubst]

@[simp] theorem diagonalRowRename {β : Type} (x : OTerm α) (j : α → β) :
    (diagonalRow x).relabel j = diagonalRow (x.relabel j) := by
  unfold diagonalRow
  rw [actualUniversalRenaming,subGraphRename]
  simp only [InternalOriginalOrderSyntaxProof.addRelabel,Term.relabel,Term.relabel_relabel]
  rfl

theorem diagonalElimination (x y : OTerm α)
    (h : Nonempty (Derivation body Gamma (diagonalRow x))) :
    Nonempty (Derivation body Gamma (subGraph y x (add x y))) := by
  obtain ⟨h⟩ := h
  have d := Derivation.universalElimination (emb y) h
  simpa only [diagonalRow,subGraphInstantiate,varBind,liftBind,addSubst] using (Nonempty.intro d)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestSubtractionSupportProof
