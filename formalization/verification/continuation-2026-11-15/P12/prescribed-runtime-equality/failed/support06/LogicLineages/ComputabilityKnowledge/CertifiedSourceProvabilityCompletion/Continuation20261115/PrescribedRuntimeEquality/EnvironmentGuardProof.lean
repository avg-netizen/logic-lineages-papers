module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentGuardProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph FullFormulaInstantiationValidity
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Validator1 of the actual runtime formula is derived from its old-coordinate
closed-term guards, not supplied as a fixed-template or acceptance premise. -/
theorem validFormula {arity n inputs ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Formula n)
 (G : List (Formula ctx)) (raw : List.Vector (Term ctx) inputs)
 (hinputs : ∀ i : Fin inputs, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (RawReflexivityDispatcher.valid I.vtag (raw.get i))))
 :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxValidator.formulaCall I.fval (.succ .zero)
   (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e)) (.succ .zero))) := by
 obtain ⟨hscan⟩ := FixedFormulaValidityProof.fixedFormulaValidity n 1 inputs e f
  arity p I.vtag I.stag I.ptag I.ctag I.atag I.h_vtag I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G raw hinputs
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p I.fval I.h_fval
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p I.fval I.stag I.ptag I.ctag etag
  I.h_fval I.h_stag I.h_ptag I.h_ctag he (.succ (.zero : Term ctx))
  (FixedFormulaSubstitution.formulaValue I.ctag I.atag raw f e)
 exact ⟨Hilbert.Local.mp (Hilbert.Local.base hcomplete) hscan⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentGuardProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.EnvironmentGuardProof
