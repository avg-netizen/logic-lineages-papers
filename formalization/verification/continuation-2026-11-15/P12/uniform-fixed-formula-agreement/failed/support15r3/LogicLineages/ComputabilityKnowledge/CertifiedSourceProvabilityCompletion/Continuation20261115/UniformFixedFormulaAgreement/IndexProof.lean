module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.BoundVariableArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open UniformClosedSubstitutionEmit
/-- Literal bound variables survive the original emitter at each binder depth.
The strict gap is discharged by original PA numeral addition, not native syntax. -/
theorem boundIndex {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (depth : Nat) (index : Fin depth) (rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2)
    (.succ (Term.numeral depth)) rest) (Term.numeral index.val) raw)
   (variableValue ctag (Term.numeral index.val)))) := by
 let gap := depth - index.val - 1
 have hgap : index.val + Nat.succ gap = depth := by
  have hi := index.isLt
  dsimp [gap]
  omega
 obtain ⟨hadd⟩ := QuotedVerifierMP.QuotationProof.numeralAdd
  (GorbowPRNumeralCalculation.Theory p) ctx index.val (Nat.succ gap)
 rw [hgap] at hadd
 obtain ⟨hb⟩ := (StatementChecks.exactInternalBranches n p etag ptag ctag he hp hc ctx
  (Term.numeral index.val) raw .zero .zero rest (Term.numeral depth) (Term.numeral gap)).2.2.2.2.2.1
 exact ⟨Derivation.mp hb hadd⟩
/-- The sole substituted variable is exactly the current binder depth. -/
theorem freeIndex {n ctx : Nat} (p : Program n) (etag ptag ctag : Nat)
 (he : (nodes p)[etag]? = some ⟨3,emitCode⟩)
 (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
 (depth : Nat) (rest raw : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (emitCall etag (stateValue ptag ctag (Term.numeral 2)
    (.succ (Term.numeral depth)) rest) (Term.numeral depth) raw) raw)) :=
 (StatementChecks.exactInternalBranches n p etag ptag ctag he hp hc ctx
  .zero raw .zero .zero rest (Term.numeral depth) .zero).2.2.2.2.2.2.1
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformFixedFormulaAgreement.IndexProof
