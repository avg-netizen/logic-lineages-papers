module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ImplicationValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FullFormulaInstantiationValidity FullFormulaInstantiationValidity.ConstructorValidityTargets RelationalSyntaxDepthTransport
theorem implication {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3) (isS : Bool)
 (I : Installation p old arithmetic x isS) (G : List (Formula ctx)) (a b : Term ctx)
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.fval a))
 (hb : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G (UniformClosedPropositional.formulaValid I.fval b)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (UniformClosedPropositional.formulaValid I.fval (PrescribedRuntimeEquality.impValue I.ctag I.atag a b))) := by
 obtain ⟨_,_,_,eqtag,_,_,_,heq⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p I.fval I.h_fval
 obtain ⟨has⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) a
 obtain ⟨hbs⟩ := LiteralSyntaxValidator.FormulaBindingProof.sound p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) b
 have hchildren : List.Forall₂ (fun task value => Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall I.stag (singleton I.ctag task) value) (.succ .zero))))
  (ConstructorStepTargets.tasks I.ptag (.zero : Term ctx) (.formula 7)) [a,b] :=
  .cons ⟨.mp (.base has) ha⟩ (.cons ⟨.mp (.base hbs) hb⟩ .nil)
 obtain ⟨himp⟩ := ConstructorValidityProof.constructorValidity n p I.stag I.ptag I.ctag I.atag
  I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G (.formula 7) .zero [a,b] hchildren
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p I.fval I.stag I.ptag I.ctag eqtag
  I.h_fval I.h_stag I.h_ptag I.h_ctag heq (.zero : Term ctx) (PrescribedRuntimeEquality.impValue I.ctag I.atag a b)
 exact ⟨.mp (.base hcomplete) himp⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ImplicationValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ImplicationValidityProof
