module

public import LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSyntaxCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowSortedSyntaxCode

def Tags : Prop := Function.Injective tagFormula ∧ Function.Injective tagTerm ∧ ∀ a b,tagFormula a≠tagTerm b

def EncodingEquality : Prop :=
  (∀ n m (φ : Formula n) (ψ : Formula m), formulaCode φ=formulaCode ψ ↔ GorbowFormulaPrefixCode.encode φ=GorbowFormulaPrefixCode.encode ψ) ∧
  (∀ n m (t : Term n) (u : Term m), termCode t=termCode u ↔ GorbowTermPrefixCode.encode t=GorbowTermPrefixCode.encode u)

def ActualInjection : Prop :=
  (∀ n, Function.Injective (formulaCode (n:=n))) ∧
  (∀ n, Function.Injective (termCode (n:=n))) ∧
  (∀ n m (φ : Formula n) (t : Term m), formulaCode φ≠termCode t) ∧ Function.Injective variableNumber

def ExactRawDecoding : Prop :=
  (∀ code raw, decodeFormulaRaw code=some raw ↔ code=formulaRawNumber raw) ∧
  (∀ code raw, decodeTermRaw code=some raw ↔ code=termRawNumber raw)

def ActualCalibration : Prop :=
  (∀ n (i : Fin n), variableNumber i.val=termCode (Term.var i)) ∧
  (∀ n (φ : Formula n), decodeFormulaRaw (formulaCode φ)=some (GorbowFormulaPrefixCode.encode φ)) ∧
  (∀ n (t : Term n), decodeTermRaw (termCode t)=some (GorbowTermPrefixCode.encode t)) ∧
  (∀ code i, decodeVariable code=some i ↔ code=variableNumber i) ∧
  (∀ code, isVariableCode code=true ↔ ∃ i,code=variableNumber i)

def QuoteSemantics : Prop :=
  (∀ n k (φ : Formula n) I ρ, (formulaQuote k φ).realize I ρ=formulaCode φ) ∧
  (∀ n k (t : Term n) I ρ, (termQuote k t).realize I ρ=termCode t)

def UniformPrograms : Prop := Primrec tagFormula ∧ Primrec tagTerm ∧
  Primrec formulaRawNumber ∧ Primrec termRawNumber ∧ Primrec variableNumber ∧
  Primrec decodeFormulaRaw ∧ Primrec decodeTermRaw ∧ Primrec decodeVariable ∧ Primrec isVariableCode

def Target : Prop := Tags ∧ EncodingEquality ∧ ActualInjection ∧ ExactRawDecoding ∧ ActualCalibration ∧ QuoteSemantics ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSortedSyntaxCode
