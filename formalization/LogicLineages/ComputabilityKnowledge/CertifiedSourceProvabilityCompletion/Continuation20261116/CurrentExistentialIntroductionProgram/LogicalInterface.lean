module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalCore
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.RuntimeRebase
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphValues
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalInterface
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality SixSol20261112.Fuel NamedArithmeticGraph
structure Nodes {n : Nat} (p : Program n) where
 lineTag : Bool → Nat
 singletonTag : Bool → Nat
 hline : ∀ b, (nodes p)[lineTag b]? = some ⟨2,OriginalQuantifierLogicalProducers.lineConstructor b⟩
 hsingle : ∀ b, (nodes p)[singletonTag b]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor b⟩
variable {n k ctx : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (x : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t
  (CurrentQuantifierLogicalSource.selectedOld rawOld) ar x)
 (N : Nodes p)
def installed (b : Bool) : CurrentQuantifierLogicalCertificate.Installation p f lhs rhs rawOld
 (CumulativePropositionalSource.arithmetic ar) x b :=
 { toInstallation := (RuntimeRebase.shared p f lhs rhs t _ ar x I).currentK
   quantifierTag := N.lineTag b
   singletonTag := N.singletonTag b
   h_quantifierTag := N.hline b
   h_singletonTag := N.hsingle b }
theorem logical (b : Bool) (G : List (Formula ctx)) (a z index fuel : Term ctx)
 (hg : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (OriginalQuantifierLogicalExtension.guards b I.currentK.fval a z)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.currentK.coreTag index fuel
   (OriginalQuantifierLogicalProducers.conclusionValue b I.previous.current.ctag I.previous.current.atag a z)
   (OriginalQuantifierLogicalProducers.lineCall (N.singletonTag b) a z))) :=
 LogicalCore.singleton p f lhs rhs rawOld _ x b (installed p f lhs rhs t rawOld ar x I N b) G a z index fuel hg
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalInterface
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.LogicalInterface
