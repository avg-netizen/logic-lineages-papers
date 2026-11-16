module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CumulativePropositionalSource
/-- Actual annotation2/10 singleton at the explicitly extended source. Only
original formula guards and actual AST memberships are premises. All arity0
conclusion validation, cumulative logical-wrapper acceptance and machine
transitions are obligations. No native calibration, logical-hit, line-validity,
CORE oracle or bound dependent on runtime syntax is assumed. Pure logical
singletons need no source-axiom fuel bound: index/fuel remain arbitrary. -/
def InternalCertificate : Prop := ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) (pF pR : Program 1),
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 let p := root f lhs rhs pF pR old ar baseX
 ∀ (I : JointInstallation p f lhs rhs t old ar (SaturatedAxiomLeaf.saturated baseX))
 (isExists : Bool) (lineTag singletonTag : Nat),
 (nodes p)[lineTag]? = some ⟨2,OriginalQuantifierLogicalProducers.lineConstructor isExists⟩ →
 (nodes p)[singletonTag]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor isExists⟩ →
 ∀ ctx (a b index fuel : Term ctx),
 let C := OriginalQuantifierLogicalProducers.conclusionValue isExists I.currentK.ctag I.currentK.atag a b
 let code := certificate singletonTag a b
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (OriginalQuantifierLogicalExtension.guards isExists I.currentK.fval a b)
   (.conj (.equal (LiteralCheckerAcceptance.runCall I.currentK.iteratorTag I.currentK.ptag index fuel code)
     (output isExists I.currentK.ptag I.currentK.ctag I.currentK.atag a b))
    (.conj (.equal (LiteralCheckerAcceptance.coreCall I.currentK.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.currentK.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.Targets
