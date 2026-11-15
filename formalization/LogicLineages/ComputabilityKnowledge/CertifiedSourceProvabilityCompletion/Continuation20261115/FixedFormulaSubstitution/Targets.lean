module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113
/-- Original full term substitution under a typed bound/free environment. -/
def NativeTerm : Prop := ∀ n depth inputs (e : Environment n depth inputs) (t : Term n) (u : Fin inputs → Term 0),
 evaluate (termProgram e t) (rawInputs u) =
 Encodable.encode (GorbowTermPrefixCode.encode (GorbowSubstitution.substitute (assignment e u) t))
/-- Original capture-correct formula substitution, including both binders and
all U/Ag/K/T syntax. Closed inputs are not evaluated. -/
def NativeFormula : Prop := ∀ n depth inputs (e : Environment n depth inputs) (f : Formula n) (u : Fin inputs → Term 0),
 evaluate (formulaProgram f e) (rawInputs u) =
 Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowFormulaSubstitution.substituteFormula (assignment e u) f))
/-- Unconditional constructor graph for arbitrary symbolic raw numeric inputs,
including malformed codes, in the actual supplied registry. -/
def InternalTerm : Prop := ∀ n depth inputs (e : Environment n depth inputs) (t : Term n)
 arity (p : Program arity) (tag ctag atag : Nat),
 (nodes p)[tag]? = some ⟨inputs,termProgram e t⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : List.Vector (Term ctx) inputs),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (call tag raw) (termValue ctag atag e raw t)))
def InternalFormula : Prop := ∀ n depth inputs (e : Environment n depth inputs) (f : Formula n)
 arity (p : Program arity) (tag ctag atag : Nat),
 (nodes p)[tag]? = some ⟨inputs,formulaProgram f e⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : List.Vector (Term ctx) inputs),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (call tag raw) (formulaValue ctag atag raw f e)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FixedFormulaSubstitution.Targets
