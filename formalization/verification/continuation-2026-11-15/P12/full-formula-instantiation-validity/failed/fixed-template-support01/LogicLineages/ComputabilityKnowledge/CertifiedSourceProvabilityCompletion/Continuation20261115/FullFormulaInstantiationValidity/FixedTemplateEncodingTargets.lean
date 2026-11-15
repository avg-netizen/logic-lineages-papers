module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedFormulaValidityStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector
open SixSol20261113 FixedFormulaSubstitution
/-- All variables are actual bound indices, with no runtime input coordinates. -/
def boundEnvironment (n : Nat) : Environment n n 0 := fun i => .inl i
/-- Exact original term code, derived by constructor equations for cons/append.
No installed quotation-program node or validator reflection is assumed. -/
def InternalBoundTermEncoding : Prop := ∀ n (t : Term n) arity (p : Program arity) ctag atag,
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (termValue ctag atag (boundEnvironment n) (nil : List.Vector (Term ctx) 0) t)
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t)))))
/-- Exact original full formula code, including both binders and all symbols.
This is code arithmetic, not an assertion that a syntax scanner evaluates to true. -/
def InternalBoundFormulaEncoding : Prop := ∀ n (f : Formula n) arity (p : Program arity) ctag atag,
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (FixedFormulaSubstitution.formulaValue ctag atag (nil : List.Vector (Term ctx) 0) f (boundEnvironment n))
   (Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.FixedTemplateEncodingTargets
