module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.UnaryValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FullFormulaInstantiationValidity FullFormulaInstantiationValidity.ConstructorValidityTargets RelationalSyntaxDepthTransport
open OriginalQuantifierLogicalExtension
theorem conclusionValidity {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedPropositionalCertificate.Installation p old arithmetic x false)
 (isExists : Bool) (a b : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (guards isExists I.fval a b)
   (formulaValid 0 I.fval (OriginalQuantifierLogicalProducers.conclusionValue isExists I.ctag I.atag a b)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := guards isExists I.fval a b
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 cases isExists with
 | false =>
  have ha : Hilbert.Local T ctx G (formulaValid 0 I.fval a) := .mp (.base (.logical (.andLeft _ _))) hh
  have hb : Hilbert.Local T ctx G (formulaValid 0 I.fval b) := .mp (.base (.logical (.andRight _ _))) hh
  obtain ⟨hna⟩ := UnaryValidityProof.unary p old arithmetic x I G 0 0 6 a rfl ha
  obtain ⟨hnb⟩ := UnaryValidityProof.unary p old arithmetic x I G 0 0 6 b rfl hb
  obtain ⟨hl⟩ := UniformClosedPropositionalCertificate.ImplicationValidityProof.implication p old arithmetic x false I G _ _ hna hnb
  obtain ⟨hr⟩ := UniformClosedPropositionalCertificate.ImplicationValidityProof.implication p old arithmetic x false I G b a hb ha
  obtain ⟨hout⟩ := UniformClosedPropositionalCertificate.ImplicationValidityProof.implication p old arithmetic x false I G _ _ hl hr
  exact ⟨hout.discharge.finish⟩
 | true =>
  have ha : Hilbert.Local T ctx G (formulaValid 1 I.fval a) := hh
  obtain ⟨hna⟩ := UnaryValidityProof.unary p old arithmetic x I G 1 1 6 a rfl ha
  obtain ⟨hall⟩ := UnaryValidityProof.unary p old arithmetic x I G 0 1 10 _ rfl hna
  obtain ⟨hleft⟩ := UnaryValidityProof.unary p old arithmetic x I G 0 0 6 _ rfl hall
  obtain ⟨hright⟩ := UnaryValidityProof.unary p old arithmetic x I G 0 1 11 a rfl ha
  obtain ⟨hout⟩ := UniformClosedPropositionalCertificate.ImplicationValidityProof.implication p old arithmetic x false I G _ _ hleft hright
  exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.ValidityProof
