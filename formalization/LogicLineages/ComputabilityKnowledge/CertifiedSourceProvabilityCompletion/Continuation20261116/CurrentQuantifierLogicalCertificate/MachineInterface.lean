module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.ValidityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate.WrapperProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
abbrev baseLogical (f : Formula 1) (lhs rhs : Term 1) (rawOld : Program 1) : Program 1 :=
 CumulativePropositionalSource.previousLogical f lhs rhs (CurrentQuantifierLogicalSource.selectedOld rawOld)
abbrev logical (f : Formula 1) (lhs rhs : Term 1) (rawOld : Program 1) : Program 1 :=
 CumulativePropositionalSource.logical f lhs rhs (CurrentQuantifierLogicalSource.selectedOld rawOld)
abbrev kernel (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3) : Program 3 :=
 UniformClosedPropositionalCertificate.kernel (baseLogical f lhs rhs rawOld) arithmetic x
abbrev checker (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3) : Program 5 :=
 UniformClosedPropositionalCertificate.checker (baseLogical f lhs rhs rawOld) arithmetic x
abbrev dispatcher (f : Formula 1) (lhs rhs : Term 1) (rawOld arithmetic : Program 1) (x : Program 3) : Program 4 :=
 UniformClosedPropositionalCertificate.dispatcher (baseLogical f lhs rhs rawOld) arithmetic x
/-- Proof interface contains only existing actual K installation and two
actual producer nodes. No runtime acceptance or validity fields. -/
structure Installation {n : Nat} (p : Program n) (f : Formula 1) (lhs rhs : Term 1)
 (rawOld arithmetic : Program 1) (x : Program 3) (isExists : Bool) extends
 UniformClosedPropositionalCertificate.Installation p (baseLogical f lhs rhs rawOld) arithmetic x false where
 quantifierTag : Nat
 singletonTag : Nat
 h_quantifierTag : (nodes p)[quantifierTag]? = some ⟨2,OriginalQuantifierLogicalProducers.lineConstructor isExists⟩
 h_singletonTag : (nodes p)[singletonTag]? = some ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor isExists⟩
def rawCertificate {ctx : Nat} (ctag quantifierTag : Nat) (a b : Term ctx) : Term ctx :=
 OriginalQuantifierLogicalProducers.singletonValue quantifierTag ctag a b

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalCertificate
