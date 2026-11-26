module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCoreRetention.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityStatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
abbrev dispatcher (old arithmetic : Program 1) (x : Program 3) : Program 4 :=
 HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator (UniformClosedPropositional.logicalLeaf old) arithmetic x
abbrev kernel (old arithmetic : Program 1) (x : Program 3) : Program 3 :=
 HistoryKernel.kernel LiteralSyntaxValidator.lineValidator (UniformClosedPropositional.logicalLeaf old) arithmetic x
abbrev checker (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 UniformClosedPropositionalCoreRetention.extended LiteralSyntaxValidator.lineValidator old arithmetic x
abbrev verifier (old arithmetic : Program 1) (x : Program 3) : Program 5 :=
 SixSol20261112.Fuel.verifier (checker old arithmetic x)
/-- Same-root memberships only. No constructor validity, dispatcher success,
run, native calibration, or source-tuple equality is supplied as a field. -/
structure Installation {n : Nat} (p : Program n) (old arithmetic : Program 1) (x : Program 3) (isS : Bool) where
 constructorTag : Nat
 ptag : Nat
 ctag : Nat
 atag : Nat
 fval : Nat
 stag : Nat
 lineTag : Nat
 logicalTag : Nat
 dispatcherTag : Nat
 iteratorTag : Nat
 coreTag : Nat
 verifierTag : Nat
 h_constructorTag : (nodes p)[constructorTag]? = some ⟨3,UniformClosedPropositional.lineConstructor isS⟩
 h_ptag : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩
 h_ctag : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩
 h_atag : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩
 h_fval : (nodes p)[fval]? = some ⟨2,LiteralSyntaxValidator.formulaValidator⟩
 h_stag : (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩
 h_lineTag : (nodes p)[lineTag]? = some ⟨1,LiteralSyntaxValidator.lineValidator⟩
 h_logicalTag : (nodes p)[logicalTag]? = some ⟨1,UniformClosedPropositional.logicalLeaf old⟩
 h_dispatcherTag : (nodes p)[dispatcherTag]? = some ⟨4,dispatcher old arithmetic x⟩
 h_iteratorTag : (nodes p)[iteratorTag]? = some ⟨4,SixSol20261112.HistoryMachine.iterator (kernel old arithmetic x)⟩
 h_coreTag : (nodes p)[coreTag]? = some ⟨5,checker old arithmetic x⟩
 h_verifierTag : (nodes p)[verifierTag]? = some ⟨5,verifier old arithmetic x⟩
def certificate {ctx : Nat} (ctag constructorTag : Nat) (a b c : Term ctx) : Term ctx :=
 UniformClosedPropositional.singletonValue constructorTag ctag a b c
def output {ctx : Nat} (isS : Bool) (ptag ctag atag : Nat) (a b c : Term ctx) : Term ctx :=
 LiteralCheckerAuxiliaries.successfulState ptag ctag .zero
  (UniformClosedPropositional.conclusionValue isS ctag atag a b c) .zero .zero
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.UniformClosedPropositionalCertificate
