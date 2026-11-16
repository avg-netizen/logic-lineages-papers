module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.CodeTransport
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate.RebaseProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalCore
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality SixSol20261112.Fuel NamedArithmeticGraph
/-- Actual annotation 2/10 singleton call, not merely its raw cons encoding. -/
theorem singleton {n ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1)
 (rawOld ar : Program 1) (x : Program 3) (isExists : Bool)
 (I : CurrentQuantifierLogicalCertificate.Installation p f lhs rhs rawOld ar x isExists)
 (G : List (Formula ctx)) (a b index fuel : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.guards isExists I.fval a b)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel
   (OriginalQuantifierLogicalProducers.conclusionValue isExists I.ctag I.atag a b)
   (OriginalQuantifierLogicalProducers.lineCall I.singletonTag a b))) := by
 obtain ⟨hc⟩ := CurrentQuantifierLogicalCertificate.CoreProof.internalCore p f lhs rhs rawOld ar x isExists I a b index fuel
 obtain ⟨he⟩ := CurrentQuantifierLogicalCertificate.CodeTransport.singleton p f lhs rhs rawOld ar x isExists I a b
 have hcore := Hilbert.Local.mp (.base hc) hg
 have hreverse := Hilbert.Local.base (Gamma := G) (Support.equalitySymmetry _ _ he)
 exact CurrentImplicationCertificate.RebaseProof.coreCode _ G I.coreTag index fuel _ _ _ hreverse hcore
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalCore
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalCore
