module

public import LogicLineages.ComputabilityKnowledge.GorbowStandardInduction

@[expose] public section

/-! An explicit classical first-order/equality and PA arithmetic core over
Gorbow's full language. Proofs have no undischarged assumptions. U/u remain
arbitrary here: source definitional syntax apparatus, completeness and
arithmetical representability are separate unpaid obligations. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowPACore
open GorbowSyntax GorbowStandardInstances

def weaken {n : Nat} (φ : Formula n) : Formula (n+1) :=
  GorbowFormulaSubstitution.substituteFormula (fun i => Term.var i.succ) φ

inductive LogicalInstance (n : Nat) where
  | k (a b : Formula n)
  | s (a b c : Formula n)
  | classicalContraposition (a b : Formula n)
  | andLeft (a b : Formula n)
  | andRight (a b : Formula n)
  | andIntro (a b : Formula n)
  | orLeft (a b : Formula n)
  | orRight (a b : Formula n)
  | orElim (a b c : Formula n)
  | existsDualForward (a : Formula (n+1))
  | existsDualBackward (a : Formula (n+1))
  | reflexive (t : Term n)
  | equalityReplace (a : Formula (n+1)) (t u : Term n)
  | allInstantiate (a : Formula (n+1)) (t : Term n)
  | allDistribute (a b : Formula (n+1))
  | allVacuous (a : Formula n)

def logicalFormula {n : Nat} : LogicalInstance n → Formula n
  | .k a b => .imp a (.imp b a)
  | .s a b c => .imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))
  | .classicalContraposition a b => .imp (.imp (.neg a) (.neg b)) (.imp b a)
  | .andLeft a b => .imp (.conj a b) a
  | .andRight a b => .imp (.conj a b) b
  | .andIntro a b => .imp a (.imp b (.conj a b))
  | .orLeft a b => .imp a (.disj a b)
  | .orRight a b => .imp b (.disj a b)
  | .orElim a b c => .imp (.imp a c) (.imp (.imp b c) (.imp (.disj a b) c))
  | .existsDualForward a => .imp (.ex a) (.neg (.all (.neg a)))
  | .existsDualBackward a => .imp (.neg (.all (.neg a))) (.ex a)
  | .reflexive t => .equal t t
  | .equalityReplace a t u => .imp (.equal t u) (.imp (instantiate a t) (instantiate a u))
  | .allInstantiate a t => .imp (.all a) (instantiate a t)
  | .allDistribute a b => .imp (.all (.imp a b)) (.imp (.all a) (.all b))
  | .allVacuous a => .imp a (.all (weaken a))

inductive ArithmeticInstance (n : Nat) where
  | succNotZero (t : Term n)
  | succInjective (t u : Term n)
  | addZero (t : Term n)
  | addSucc (t u : Term n)
  | mulZero (t : Term n)
  | mulSucc (t u : Term n)
  | induction (a : Formula (n+1))

def arithmeticFormula {n : Nat} : ArithmeticInstance n → Formula n
  | .succNotZero t => .neg (.equal (.succ t) .zero)
  | .succInjective t u => .imp (.equal (.succ t) (.succ u)) (.equal t u)
  | .addZero t => .equal (.add t .zero) t
  | .addSucc t u => .equal (.add t (.succ u)) (.succ (.add t u))
  | .mulZero t => .equal (.mul t .zero) .zero
  | .mulSucc t u => .equal (.mul t (.succ u)) (.add (.mul t u) t)
  | .induction a => GorbowStandardInduction.inductionAxiom a

inductive Proof : {n : Nat} → Formula n → Type
  | logical {n} (w : LogicalInstance n) : Proof (logicalFormula w)
  | arithmetic {n} (w : ArithmeticInstance n) : Proof (arithmeticFormula w)
  | mp {n} {a b : Formula n} : Proof (.imp a b) → Proof a → Proof b
  | generalize {n} {a : Formula (n+1)} : Proof a → Proof (.all a)
end LogicLineages.ComputabilityKnowledge.GorbowPACore
