module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransferConnectivesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.ArithmeticRules
open GorbowSyntax GorbowTheoryProof Hilbert
open LogicLineages.OrdinalComparison.TerminationOrdering
open Syntax Connectives

/-- Every arithmetic axiom, including full parameter-preserving induction,
compiles to the ORIGINAL PA(L) Hilbert rules over arbitrary extra theory T. -/
noncomputable def arithmetic {T : Sentence → Prop} {alpha : Type} {m : Nat}
    (w : ID1Completion.InternalCalculus.ArithmeticInstance alpha) (rho : alpha → Term m) :
    Derivation T (translate (ID1Completion.InternalCalculus.arithmeticFormula w) rho) := by
  cases w with
  | successorNotZero t =>
      have he := translateArithmeticEquality
        (OrdinaryArithmetic.succTerm t) OrdinaryArithmetic.zeroTerm rho
      change Derivation T (.imp
        (translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula
          ((OrdinaryArithmetic.succTerm t).equal OrdinaryArithmetic.zeroTerm)) rho) falsity)
      rw [he]
      have h := Derivation.arithmetic (A := T) (.succNotZero
        (translateTerm rho (PositiveArithmeticOperators.arithmeticEmbedding.onTerm t)))
      exact .mp (Logic.negToFalse _) h
  | successorInjective t u =>
      change Derivation T (.imp
        (translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula
          ((OrdinaryArithmetic.succTerm t).equal (OrdinaryArithmetic.succTerm u))) rho)
        (translate (PositiveArithmeticOperators.arithmeticEmbedding.onFormula (t.equal u)) rho))
      rw [translateArithmeticEquality,translateArithmeticEquality]
      exact .arithmetic (.succInjective _ _)
  | additionZero t =>
      rw [ID1Completion.InternalCalculus.arithmeticFormula,translateArithmeticEquality]
      exact .arithmetic (.addZero _)
  | additionSuccessor t u =>
      rw [ID1Completion.InternalCalculus.arithmeticFormula,translateArithmeticEquality]
      exact .arithmetic (.addSucc _ _)
  | multiplicationZero t =>
      rw [ID1Completion.InternalCalculus.arithmeticFormula,translateArithmeticEquality]
      exact .arithmetic (.mulZero _)
  | multiplicationSuccessor t u =>
      rw [ID1Completion.InternalCalculus.arithmeticFormula,translateArithmeticEquality]
      exact .arithmetic (.mulSucc _ _)
  | induction a =>
      let base := ID1Completion.InternalCalculus.instantiate a
        (PositiveArithmeticOperators.arithmeticEmbedding.onTerm OrdinaryArithmetic.zeroTerm)
      let step := SourceComputabilityFormulaSupportProof.allOne
        (a.imp (ID1Completion.InternalCalculus.successorInstance a))
      have hb : translate base rho =
          GorbowStandardInstances.instantiate (translate a (liftMap rho)) .zero :=
        translateInstantiate a
          (PositiveArithmeticOperators.arithmeticEmbedding.onTerm OrdinaryArithmetic.zeroTerm) rho
      have hs : translate step rho = Formula.all (.imp (translate a (liftMap rho))
          (GorbowStandardInduction.successorInstance (translate a (liftMap rho)))) := by
        rw [translateAllOne]
        change Formula.all (.imp _ (translate
          (ID1Completion.InternalCalculus.successorInstance a) (liftMap rho))) = _
        rw [translateSuccessorInstance]
        rfl
      have hg : translate (SourceComputabilityFormulaSupportProof.allOne a) rho =
          Formula.all (translate a (liftMap rho)) := translateAllOne a rho
      change Derivation T (.imp (translate (base ⊓ step) rho)
        (translate (SourceComputabilityFormulaSupportProof.allOne a) rho))
      rw [translateConjunction,hg,hb,hs]
      let p := translate a (liftMap rho)
      let premise := Logic.pair (GorbowStandardInstances.instantiate p .zero)
        (.all (.imp p (GorbowStandardInduction.successorInstance p)))
      change Derivation T (closeAssumptions [premise] (.all p))
      apply Logic.dischargeAll
      have hpair : Local T m [premise] premise := .hypothesis List.mem_cons_self
      exact .mp (.mp (.base (.arithmetic (.induction p)))
        (Logic.pairLeft hpair)) (Logic.pairRight hpair)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.ArithmeticTransfer.ArithmeticRules
