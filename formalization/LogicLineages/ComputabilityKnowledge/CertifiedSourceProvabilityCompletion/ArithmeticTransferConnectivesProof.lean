module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferSyntaxProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferLogicProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Connectives
open GorbowSyntax
open LogicLineages.OrdinalComparison.TerminationOrdering
open Syntax

variable {alpha : Type} {m : Nat}

theorem translateConjunction (a b : SourceFormula alpha) (rho : alpha → Term m) :
    translate (a ⊓ b) rho = Logic.pair (translate a rho) (translate b rho) := rfl

theorem translateExistsOne (a : SourceFormula (alpha ⊕ Fin 1)) (rho : alpha → Term m) :
    translate (SourceComputabilityFormulaSupportProof.existsOne a) rho =
      Logic.encodedExists (translate a (liftMap rho)) := by
  change Formula.imp
    (translate (SourceComputabilityFormulaSupportProof.allOne a.not) rho) falsity = _
  rw [translateAllOne]
  rfl

theorem translateSuccessorInstance (a : SourceFormula (alpha ⊕ Fin 1)) (rho : alpha → Term m) :
    translate (ID1Completion.InternalCalculus.successorInstance a) (liftMap rho) =
      GorbowStandardInduction.successorInstance (translate a (liftMap rho)) := by
  rw [ID1Completion.InternalCalculus.successorInstance,translateSourceSubstitution]
  rw [GorbowStandardInduction.successorInstance,translateGorbowSubstitution]
  apply congrArg (translate a)
  funext x
  cases x with
  | inl x =>
      change GorbowFormulaSubstitution.renameTerm Fin.succ (rho x) =
        GorbowSubstitution.substitute
          (Fin.cases (.succ (.var 0)) (fun i : Fin m => .var i.succ))
          (GorbowFormulaSubstitution.renameTerm Fin.succ (rho x))
      unfold GorbowFormulaSubstitution.renameTerm
      rw [GorbowSubstitution.substitute_composition]
      apply congrArg (fun sigma : Fin m → Term (m+1) => GorbowSubstitution.substitute sigma (rho x))
      funext i
      simp only [GorbowSubstitution.substitute,Fin.cases_succ]
  | inr i => rfl

private theorem embeddingRelabel {beta : Type} (g : alpha → beta) (t : OrdinaryArithmetic.Term alpha) :
    PositiveArithmeticOperators.arithmeticEmbedding.onTerm (t.relabel g) =
      (PositiveArithmeticOperators.arithmeticEmbedding.onTerm t).relabel g := by
  induction t with
  | var i => rfl
  | func f ts ih =>
      change FirstOrder.Language.Term.func _
        (fun i => PositiveArithmeticOperators.arithmeticEmbedding.onTerm ((ts i).relabel g)) =
        FirstOrder.Language.Term.func _
          (fun i => (PositiveArithmeticOperators.arithmeticEmbedding.onTerm (ts i)).relabel g)
      exact congrArg (FirstOrder.Language.Term.func _) (funext ih)

theorem translateArithmeticEquality (t u : OrdinaryArithmetic.Term alpha) (rho : alpha → Term m) :
    translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula (t.equal u)) rho =
      Formula.equal
        (translateTerm rho (PositiveArithmeticOperators.arithmeticEmbedding.onTerm t))
        (translateTerm rho (PositiveArithmeticOperators.arithmeticEmbedding.onTerm u)) := by
  have he : PositiveArithmeticOperators.arithmeticEmbedding.onFormula (t.equal u) =
      (PositiveArithmeticOperators.arithmeticEmbedding.onTerm t).equal
        (PositiveArithmeticOperators.arithmeticEmbedding.onTerm u) := by
    unfold FirstOrder.Language.Term.equal FirstOrder.Language.LHom.onFormula
      FirstOrder.Language.LHom.onBoundedFormula FirstOrder.Language.Term.bdEqual
    change FirstOrder.Language.BoundedFormula.equal
      (PositiveArithmeticOperators.arithmeticEmbedding.onTerm (t.relabel Sum.inl))
      (PositiveArithmeticOperators.arithmeticEmbedding.onTerm (u.relabel Sum.inl)) =
      FirstOrder.Language.BoundedFormula.equal
        ((PositiveArithmeticOperators.arithmeticEmbedding.onTerm t).relabel Sum.inl)
        ((PositiveArithmeticOperators.arithmeticEmbedding.onTerm u).relabel Sum.inl)
    rw [embeddingRelabel,embeddingRelabel]
  rw [he,translateEquality]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.Connectives
