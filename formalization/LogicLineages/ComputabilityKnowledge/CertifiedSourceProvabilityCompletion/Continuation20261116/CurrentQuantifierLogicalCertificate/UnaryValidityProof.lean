module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.UnaryValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FullFormulaInstantiationValidity FullFormulaInstantiationValidity.ConstructorValidityTargets RelationalSyntaxDepthTransport
open OriginalQuantifierLogicalExtension
theorem unary {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedPropositionalCertificate.Installation p old arithmetic x false)
 (G : List (Formula ctx)) (arity childArity : Nat) (token : Fin 12) (a : Term ctx)
 (hrow : ConstructorStepTargets.tasks I.ptag (Term.numeral arity : Term ctx) (.formula token) =
  [LiteralSyntaxStep.taskCall I.ptag 1 (Term.numeral childArity)])
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (formulaValid childArity I.fval a)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (formulaValid arity I.fval (FixedFormulaSubstitution.unaryValue I.ctag token.val a))) := by
 obtain ⟨_,_,_,eqtag,_,_,_,heq⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p I.fval I.h_fval
 obtain ⟨has⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (Term.numeral childArity : Term ctx) a
 have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (Term.numeral arity : Term ctx) (.formula token)) [a] := by
  rw [hrow]
  exact .cons ⟨.mp (.base has) ha⟩ .nil
 obtain ⟨hout⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula token) (Term.numeral arity) [a] hchildren
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (Term.numeral arity : Term ctx)
  (FixedFormulaSubstitution.unaryValue I.ctag token.val a)
 exact ⟨.mp (.base hcomplete) hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.UnaryValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.UnaryValidityProof
