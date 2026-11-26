module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ImplicationValidityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ValidityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open FullFormulaInstantiationValidity FullFormulaInstantiationValidity.ConstructorValidityTargets RelationalSyntaxDepthTransport
theorem conclusionValidity {n ctx : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3) (isS : Bool)
 (I : Installation p old arithmetic x isS) (a b c : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedPropositional.guards isS I.fval a b c)
   (UniformClosedPropositional.formulaValid I.fval (UniformClosedPropositional.conclusionValue isS I.ctag I.atag a b c)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := UniformClosedPropositional.guards isS I.fval a b c
 let G := [H]
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hA : Hilbert.Local T ctx G (UniformClosedPropositional.formulaValid I.fval a) := .mp (.base (.logical (.andLeft _ _))) hh
 have hRest := Hilbert.Local.mp (.base (.logical (.andRight _ _))) hh
 cases isS with
 | false =>
  obtain ⟨hba⟩ := ImplicationValidityProof.implication p old arithmetic x false I G b a hRest hA
  obtain ⟨hout⟩ := ImplicationValidityProof.implication p old arithmetic x false I G a _ hA hba
  exact ⟨hout.discharge.finish⟩
 | true =>
  have hB : Hilbert.Local T ctx G (UniformClosedPropositional.formulaValid I.fval b) := .mp (.base (.logical (.andLeft _ _))) hRest
  have hC : Hilbert.Local T ctx G (UniformClosedPropositional.formulaValid I.fval c) := .mp (.base (.logical (.andRight _ _))) hRest
  obtain ⟨hbc⟩ := ImplicationValidityProof.implication p old arithmetic x true I G b c hB hC
  obtain ⟨habc⟩ := ImplicationValidityProof.implication p old arithmetic x true I G a _ hA hbc
  obtain ⟨hab⟩ := ImplicationValidityProof.implication p old arithmetic x true I G a b hA hB
  obtain ⟨hac⟩ := ImplicationValidityProof.implication p old arithmetic x true I G a c hA hC
  obtain ⟨hright⟩ := ImplicationValidityProof.implication p old arithmetic x true I G _ _ hab hac
  obtain ⟨hout⟩ := ImplicationValidityProof.implication p old arithmetic x true I G _ _ habc hright
  exact ⟨hout.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.ValidityProof
