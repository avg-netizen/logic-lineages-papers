module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Actual K/S singleton computation and CORE/Fuel acceptance at identical
index/fuel/code, for arbitrary runtime raw codes guarded only by the original
closed-formula validators. Iteration count is encoded certificate NUMBER, not
list length. The unused K third input is not required valid. This supplies no
same-new-root published-source reinstallation and is not HB3. -/
def InternalCertificate : Prop := ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3) isS
 (I : Installation p old arithmetic x isS), ∀ ctx (a b c index fuel : Term ctx),
 let C := UniformClosedPropositional.conclusionValue isS I.ctag I.atag a b c
 let code := certificate I.ctag I.constructorTag a b c
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (UniformClosedPropositional.guards isS I.fval a b c)
   (.conj (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code)
     (output isS I.ptag I.ctag I.atag a b c))
    (.conj (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add C C) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add C C) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate.Targets
