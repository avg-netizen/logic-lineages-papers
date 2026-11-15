module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.EmitterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.KindProof
open GorbowSyntax GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
/-- Recover the new kind from the actual relation's alternatives, excluding
its index alternative by an internal arithmetic disequality, not a shape axiom. -/
theorem ordinary (T : Sentence → Prop) {ctx : Nat} (l r : Nat) (a b k : Term ctx)
 (hne : Derivation T (.neg (.equal k (Term.numeral 2)))) :
 Nonempty (Derivation T (.imp (taskRelation l r a b)
  (.imp (.equal (call l (a ::ᵥ nil)) k) (.equal (call l (b ::ᵥ nil)) k)))) := by
 let H := taskRelation l r a b
 let K := Formula.equal (call l (a ::ᵥ nil)) k
 let Q := Formula.equal (call l (b ::ᵥ nil)) k
 let A := Formula.conj (.equal (call l (a ::ᵥ nil)) (call l (b ::ᵥ nil)))
  (.disj (.equal (call l (a ::ᵥ nil)) .zero) (.equal (call l (a ::ᵥ nil)) (Term.numeral 1)))
 let B := Formula.conj (.equal (call l (a ::ᵥ nil)) (Term.numeral 2)) (.equal (call l (b ::ᵥ nil)) .zero)
 have ha : Hilbert.Local T ctx [A,K,H] A := .hypothesis (by simp)
 have hk : Hilbert.Local T ctx [A,K,H] K := .hypothesis (by simp)
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) ha
 have qa : Hilbert.Local T ctx [K,H] (.imp A Q) :=
  (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) hk).discharge
 have hb : Hilbert.Local T ctx [B,K,H] B := .hypothesis (by simp)
 have hk' : Hilbert.Local T ctx [B,K,H] K := .hypothesis (by simp)
 have he' := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hb
 have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hk') he'
 have qb : Hilbert.Local T ctx [K,H] (.imp B Q) := (Hilbert.Local.explosion Q hbad (.base hne)).discharge
 have hh : Hilbert.Local T ctx [K,H] H := .hypothesis (by simp)
 have hor : Hilbert.Local T ctx [K,H] (.disj A B) := .mp (.base (.logical (.andRight _ _))) hh
 exact ⟨(Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim A B Q))) qa) qb) hor).discharge.discharge.finish⟩
/-- A pending old index can only use the index/term alternative. Ordinary
term/formula alternatives contradict its actual decoded kind2 internally. -/
theorem index (T : Sentence → Prop) {ctx : Nat} (l r : Nat) (a b : Term ctx) :
 Nonempty (Derivation T (.imp (taskRelation l r a b)
  (.imp (.equal (call l (a ::ᵥ nil)) (Term.numeral 2)) (.equal (call l (b ::ᵥ nil)) .zero)))) := by
 let H := taskRelation l r a b
 let K := Formula.equal (call l (a ::ᵥ nil)) (Term.numeral 2)
 let Q := Formula.equal (call l (b ::ᵥ nil)) .zero
 let Z := Formula.equal (call l (a ::ᵥ nil)) .zero
 let O := Formula.equal (call l (a ::ᵥ nil)) (Term.numeral 1)
 let A := Formula.conj (.equal (call l (a ::ᵥ nil)) (call l (b ::ᵥ nil))) (.disj Z O)
 let B := Formula.conj K Q
 have hz : Hilbert.Local T ctx [Z,A,K,H] Z := .hypothesis (by simp)
 have hkz : Hilbert.Local T ctx [Z,A,K,H] K := .hypothesis (by simp)
 have hbadz := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hkz) hz
 have qz : Hilbert.Local T ctx [A,K,H] (.imp Z Q) :=
  (Hilbert.Local.explosion Q hbadz (.base (.arithmetic (.succNotZero (.succ .zero))))).discharge
 have ho : Hilbert.Local T ctx [O,A,K,H] O := .hypothesis (by simp)
 have hko : Hilbert.Local T ctx [O,A,K,H] K := .hypothesis (by simp)
 have hbado := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ ho) hko
 obtain ⟨hne⟩ := EmitterProof.oneNotTwo T ctx
 have qo : Hilbert.Local T ctx [A,K,H] (.imp O Q) := (Hilbert.Local.explosion Q hbado (.base hne)).discharge
 have ha : Hilbert.Local T ctx [A,K,H] A := .hypothesis (by simp)
 have hor : Hilbert.Local T ctx [A,K,H] (.disj Z O) := .mp (.base (.logical (.andRight _ _))) ha
 have qa : Hilbert.Local T ctx [K,H] (.imp A Q) :=
  (Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim Z O Q))) qz) qo) hor).discharge
 have hb : Hilbert.Local T ctx [B,K,H] B := .hypothesis (by simp)
 have qb : Hilbert.Local T ctx [K,H] (.imp B Q) :=
  (Hilbert.Local.mp (.base (.logical (.andRight _ _))) hb).discharge
 have hh : Hilbert.Local T ctx [K,H] H := .hypothesis (by simp)
 have hor' : Hilbert.Local T ctx [K,H] (.disj A B) := .mp (.base (.logical (.andRight _ _))) hh
 exact ⟨(Hilbert.Local.mp (.mp (.mp (.base (.logical (.orElim A B Q))) qa) qb) hor').discharge.discharge.finish⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.KindProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport.KindProof
