module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.TemplateProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open RelationalSyntaxDepthTransport ConstructorValidityTargets FixedTemplateEncodingTargets
theorem validTemplate {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x) (f : Formula 1) (ctx : Nat) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (LiteralSyntaxValidator.formulaCall I.fval (.succ .zero)
   (Term.numeral (n := ctx) (FullFormulaInstantiation.templateCode f))) (.succ .zero))) := by
 let G : List (Formula ctx) := []
 let stag := I.stag
 let ptag := I.ptag
 let ctag := I.ctag
 let atag := I.atag
 obtain ⟨htemplate⟩ := FixedFormulaValidityProof.fixedFormulaValidity 1 1 0 (boundEnvironment 1) f
  n p I.vtag I.stag I.ptag I.ctag I.atag I.h_vtag I.h_stag I.h_ptag I.h_ctag I.h_atag ctx G nil (fun i => Fin.elim0 i)
 obtain ⟨hcode⟩ := FixedTemplateEncodingProof.boundFormulaEncoding 1 f n p I.ctag I.atag I.h_ctag I.h_atag ctx
 let symbolic := FixedFormulaSubstitution.formulaValue ctag atag (nil : List.Vector (Term ctx) 0) f (boundEnvironment 1)
 let literal := Term.numeral (n := ctx) (FullFormulaInstantiation.templateCode f)
 have hscan := Logic.callCongruence (ctx := ctx) (GorbowPRNumeralCalculation.Theory p) stag
  (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (Term.numeral 1)) ::ᵥ symbolic ::ᵥ nil)
  (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (Term.numeral 1)) ::ᵥ literal ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .logical (.reflexive _)
   | succ i => cases i using Fin.cases with
     | zero => exact hcode
     | succ i => exact Fin.elim0 i)
 have htemplateLiteral : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (LiteralSyntaxScan.scanCall stag
   (singleton ctag (LiteralSyntaxStep.taskCall ptag 1 (.succ .zero))) literal) (.succ .zero)) :=
  localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hscan)) htemplate
 obtain ⟨_,_,_,etag,_,_,_,he⟩ := LiteralSyntaxValidator.FormulaBindingProof.nodesInstalled p I.fval I.h_fval
 obtain ⟨hcomplete⟩ := LiteralSyntaxValidator.FormulaBindingProof.complete p I.fval I.stag I.ptag I.ctag etag
  I.h_fval I.h_stag I.h_ptag I.h_ctag he (.succ (.zero : Term ctx)) literal
 exact ⟨(Hilbert.Local.mp (Hilbert.Local.base hcomplete) htemplateLiteral).finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.TemplateProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.TemplateProof
