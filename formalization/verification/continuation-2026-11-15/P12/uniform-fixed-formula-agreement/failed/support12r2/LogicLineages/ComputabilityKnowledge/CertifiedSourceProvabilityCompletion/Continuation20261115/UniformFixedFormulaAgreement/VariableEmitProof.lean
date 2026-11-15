module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.TraversalDefinitions
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.PrefixCodeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableEmitProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph Traversal
/-- Original index emission equals the exact capture-correct variable value:
every bound index is copied and the sole free index emits the runtime raw term. -/
theorem exactValue {n ctx : Nat} (p : Program n) (I : Installation p)
 (depth : Nat) (index : Fin (depth+1)) (rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (UniformClosedSubstitutionEmit.emitCall I.etag
   (UniformClosedSubstitutionEmit.stateValue I.ptag I.ctag (Term.numeral 2)
    (.succ (Term.numeral depth)) rest) (Term.numeral index.val) raw)
   (FixedFormulaSubstitution.termValue I.ctag I.atag (EnvironmentProof.environment depth)
    (raw ::ᵥ nil) (.var index)))) := by
 by_cases h : index.val < depth
 · simp only [FixedFormulaSubstitution.termValue, EnvironmentProof.environment, dif_pos h]
   obtain ⟨he⟩ := IndexProof.boundIndex p I.etag I.ptag I.ctag I.he I.hp I.hc
    depth ⟨index.val,h⟩ rest raw
   obtain ⟨hc⟩ := PrefixCodeProof.encoded p I.ctag I.hc [0,index.val] (ctx := ctx)
   have hc' : Derivation (GorbowPRNumeralCalculation.Theory p)
    (.equal (UniformClosedSubstitutionEmit.variableValue (ctx := ctx) I.ctag (Term.numeral index.val))
     (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (⟨index.val,h⟩ : Fin depth)))))) := by
    simpa only [UniformClosedSubstitutionEmit.variableValue,UniformClosedSubstitutionEmit.singletonValue,
     SegmentProof.tokenPrefix,GorbowTermPrefixCode.encode,Term.numeral] using hc
   exact ⟨Logic.trans _ _ _ he hc'⟩
 · have hi : index.val = depth := by have hb := index.isLt; omega
   simp only [FixedFormulaSubstitution.termValue, EnvironmentProof.environment, dif_neg h,
    List.Vector.get_cons_zero]
   rw [hi]
   exact IndexProof.freeIndex p I.etag I.ptag I.ctag I.he I.hp I.hc depth rest raw
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableEmitProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.VariableEmitProof
