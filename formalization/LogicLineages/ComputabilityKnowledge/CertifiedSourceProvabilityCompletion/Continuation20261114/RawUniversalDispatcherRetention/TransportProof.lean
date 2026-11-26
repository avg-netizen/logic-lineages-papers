module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.TransportProof
open GorbowPRDefiningEquations GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof List.Vector SixSol20261113
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryRuleSuffix
open HistoryDispatcher.SelectProof

def Preserves {k : Nat} (q q' : Program k) : Prop := ∀ n (p : Program n) tag tag',
 (nodes p)[tag]? = some ⟨k,q⟩ → (nodes p)[tag']? = some ⟨k,q'⟩ →
 ∀ ctx (args : List.Vector (Term ctx) k),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (accepts (call tag args)) (accepts (call tag' args))))

theorem reflexive {k : Nat} (q : Program k) : Preserves q q := by
 intro n p tag tag' ht ht' ctx args
 obtain ⟨he⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tag' tag k q ht' ht ctx args
 let H := accepts (call tag args)
 have hh : Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx [H] H := .hypothesis List.mem_cons_self
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base he) hh))⟩

theorem choose {k : Nat} (t a b a' b' : Program k)
 (ha : Preserves a a') (hb : Preserves b b') :
 Preserves (HistoryRuleSuffix.choose t a b) (HistoryRuleSuffix.choose t a' b') := by
 intro n p tag tag' ht ht' ctx args
 let T := GorbowPRNumeralCalculation.Theory p
 let g : Fin 3 → Program k := Fin.cases t (Fin.cases a (Fin.cases b Fin.elim0))
 let g' : Fin 3 → Program k := Fin.cases t (Fin.cases a' (Fin.cases b' Fin.elim0))
 let tt := tag+argumentTag HistoryCodec.select g 0
 let ta := tag+argumentTag HistoryCodec.select g 1
 let tb := tag+argumentTag HistoryCodec.select g 2
 let tt' := tag'+argumentTag HistoryCodec.select g' 0
 let ta' := tag'+argumentTag HistoryCodec.select g' 1
 let tb' := tag'+argumentTag HistoryCodec.select g' 2
 have htest := Equations.argumentChild p tag HistoryCodec.select g ht 0
 have hayes := Equations.argumentChild p tag HistoryCodec.select g ht 1
 have hbno := Equations.argumentChild p tag HistoryCodec.select g ht 2
 have htest' := Equations.argumentChild p tag' HistoryCodec.select g' ht' 0
 have hayes' := Equations.argumentChild p tag' HistoryCodec.select g' ht' 1
 have hbno' := Equations.argumentChild p tag' HistoryCodec.select g' ht' 2
 have hsel := Equations.functionChild p tag HistoryCodec.select g ht
 have hsel' := Equations.functionChild p tag' HistoryCodec.select g' ht'
 obtain ⟨testeq⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p tt' tt k t htest' htest ctx args
 obtain ⟨ay⟩ := ha n p ta ta' hayes hayes' ctx args
 obtain ⟨bn⟩ := hb n p tb tb' hbno hbno' ctx args
 obtain ⟨oldEq⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag k 3 HistoryCodec.select g ht ctx args
 obtain ⟨newEq⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag' k 3 HistoryCodec.select g' ht' ctx args
 have oe : Derivation T (.equal (call tag args) (call (tag+1) (call tt args ::ᵥ call ta args ::ᵥ call tb args ::ᵥ nil))) := oldEq
 have ne : Derivation T (.equal (call tag' args) (call (tag'+1) (call tt' args ::ᵥ call ta' args ::ᵥ call tb' args ::ᵥ nil))) := newEq
 obtain ⟨tr⟩ := selectTransport p (tag+1) hsel (call tt args) (call ta args) (call tb args) (call ta' args) (call tb' args)
 obtain ⟨sc⟩ := GorbowPRInternalCoherence.Proof.registryCoherence n p (tag'+1) (tag+1) 3 HistoryCodec.select hsel' hsel ctx
  (call tt' args ::ᵥ call ta' args ::ᵥ call tb' args ::ᵥ nil)
 let H := accepts (call tag args)
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have oldAccept := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ oe)) hh
 have selected := Hilbert.Local.mp (.base (.mp (.mp tr ay) bn)) oldAccept
 have changed := HistoryDecoder.SelectGraphProof.testCongruence (G := [H]) (tag+1)
  (call tt' args) (call tt args) (call ta' args) (call tb' args) (.base testeq)
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (localTrans _ _ _ (.base ne) (localTrans _ _ _ (.base sc) (localTrans _ _ _ changed selected))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.TransportProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.TransportProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalDispatcherRetention.TransportProof.choose
