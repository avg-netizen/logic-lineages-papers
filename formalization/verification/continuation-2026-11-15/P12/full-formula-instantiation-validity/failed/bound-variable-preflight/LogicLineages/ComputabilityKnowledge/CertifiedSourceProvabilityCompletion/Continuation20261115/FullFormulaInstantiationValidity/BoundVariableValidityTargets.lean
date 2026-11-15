module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Exact original bound-variable prefix [0,index], at its fixed finite binder
context. The index inequality is supplied by Fin depth, never by native validator
reflection. The encoded numeral is precisely FixedFormulaSubstitution.termValue's
in-scope-variable case, not a substitute symbolic raw representation. -/
def InternalBoundVariableValidity : Prop := ∀ (depth : Nat) (index : Fin depth)
 n (p : Program n) (stag ptag ctag atag : Nat),
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxScan.scanCall stag
   (ClosedTermDepthTargets.tasks ptag ctag (Term.numeral (ctx := ctx) depth))
   (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (Term.var index))))) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableValidityTargets
