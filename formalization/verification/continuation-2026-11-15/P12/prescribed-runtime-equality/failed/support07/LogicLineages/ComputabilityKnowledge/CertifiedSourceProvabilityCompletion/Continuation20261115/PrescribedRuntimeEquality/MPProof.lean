module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MPProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Private actual-checker MP; no semantic implication or success axiom. -/
theorem one {arity ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x) (mtag : Nat)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (G : List (Formula ctx)) (A B seed ant index fuel : Term ctx)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel (impValue I.ctag I.atag A B) seed))
 (ha : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel A ant)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel B (LiteralMPRun.certificate mtag .zero B seed ant))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 have hinput : Hilbert.Local T ctx G
  (LiteralCoreMP.inputAcceptance I.coreTag I.atag I.ctag .zero A B seed ant index fuel) :=
  .mp (.mp (.base (.logical (.andIntro _ _))) hs) ha
 have hd := SixSol20261112.Fuel.Equations.argumentChild p I.qtag HistoryLookup.reference
  (fun _ : Fin 1 => HistoryLookup.drop) I.h_qtag 0
 obtain ⟨hmp⟩ := LiteralCoreMP.StatementChecks.coreMP
  (UniformClosedRule12.logicalLeaf old) arithmetic x arity p
  I.iteratorTag I.len I.atag I.ptag I.ctag I.rtag (HistoryLookup.LookupProof.dropTag I.qtag)
  I.qtag I.dispatcherTag I.h_iterator I.h_len I.h_atag I.h_ptag I.h_ctag I.h_rtag hd I.h_qtag I.h_dispatcher
  mtag I.coreTag hm I.h_core ctx .zero A B seed ant index fuel
 exact ⟨Hilbert.Local.mp (Hilbert.Local.base hmp) hinput⟩
/-- The exact nested original two-MP call. Only this private helper exposes
its three checked inputs; final recipes derive seed and unary reflexive input. -/
theorem two {arity ctx : Nat} (p : Program arity) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule12Certificate.Installation p old arithmetic x) (mtag : Nat)
 (hm : (nodes p)[mtag]? = some ⟨4,LiteralRawMP.constructor⟩)
 (G : List (Formula ctx)) (A B C seed first second index fuel : Term ctx)
 (hs : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel (impValue I.ctag I.atag A (impValue I.ctag I.atag B C)) seed))
 (hf : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel A first))
 (ht : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (core I.coreTag index fuel B second)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (accepted I.coreTag I.verifierTag index fuel C
   (LiteralMPRun.certificate mtag .zero C
    (LiteralMPRun.certificate mtag .zero (impValue I.ctag I.atag B C) seed first) second))) := by
 obtain ⟨hfirst⟩ := one p old arithmetic x I mtag hm G A (impValue I.ctag I.atag B C) seed first index fuel hs hf
 obtain ⟨hout⟩ := one p old arithmetic x I mtag hm G B C
  (LiteralMPRun.certificate mtag .zero (impValue I.ctag I.atag B C) seed first) second index fuel hfirst ht
 obtain ⟨hinj⟩ := FuelWitness.InjectionPointwiseProof.coreIntoVerifier
  p I.verifierTag I.coreTag (UniformClosedRule12Certificate.checker old arithmetic x) I.h_verifier I.h_core
  index fuel .zero (.add C C)
  (LiteralMPRun.certificate mtag .zero C
   (LiteralMPRun.certificate mtag .zero (impValue I.ctag I.atag B C) seed first) second)
 have hfuel := Hilbert.Local.mp (Hilbert.Local.base (Gamma := G) hinj) hout
 exact ⟨Hilbert.Local.mp (.mp (.base (.logical (.andIntro _ _))) hout) hfuel⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MPProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality.MPProof
