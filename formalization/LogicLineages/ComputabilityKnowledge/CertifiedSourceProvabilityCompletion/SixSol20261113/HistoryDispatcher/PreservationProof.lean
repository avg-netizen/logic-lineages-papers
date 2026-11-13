module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.SelectProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.PreservationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix IndependenceProof SelectProof

def Preserves (q : Program 4) : Prop := ∀ arity (p : Program arity) tag atag,
  (nodes p)[tag]? = some ⟨4,q⟩ → (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
  ∀ ctx (index fuel h tail line : Term ctx),
  Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
    (.imp (accepts (call tag (args index fuel h line)))
      (accepts (call tag (args index fuel (HistoryAppend.appendCall atag h tail) line)))))

theorem independentPreserves {q : Program 4} (hq : Independent q) : Preserves q := by
  intro arity p tag atag ht ha ctx index fuel h tail line
  let T := GorbowPRNumeralCalculation.Theory p
  let E := accepts (call tag (args index fuel h line))
  obtain ⟨he⟩ := independentEquation hq arity p tag ht ctx index fuel (HistoryAppend.appendCall atag h tail) h line
  have old : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ (.base he) old))⟩

theorem choosePreserves {t a b : Program 4} (ht : Independent t) (ha : Preserves a) (hb : Preserves b) :
    Preserves (choose t a b) := by
  intro arity p tag atag hnode happ ctx index fuel h tail line
  let T := GorbowPRNumeralCalculation.Theory p
  let g : Fin 3 → Program 4 := Fin.cases t (Fin.cases a (Fin.cases b Fin.elim0))
  let ot := args index fuel h line
  let nt := args index fuel (HistoryAppend.appendCall atag h tail) line
  let tt := tag+argumentTag HistoryCodec.select g 0
  let ta := tag+argumentTag HistoryCodec.select g 1
  let tb := tag+argumentTag HistoryCodec.select g 2
  have htest := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g hnode 0
  have hayes := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g hnode 1
  have hbno := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g hnode 2
  have hsel := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select g hnode
  obtain ⟨testeq⟩ := independentEquation ht arity p tt htest ctx index fuel (HistoryAppend.appendCall atag h tail) h line
  obtain ⟨ay⟩ := ha arity p ta atag hayes happ ctx index fuel h tail line
  obtain ⟨bn⟩ := hb arity p tb atag hbno happ ctx index fuel h tail line
  obtain ⟨oldEq⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation arity p tag 4 3 HistoryCodec.select g hnode ctx ot
  obtain ⟨newEq⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation arity p tag 4 3 HistoryCodec.select g hnode ctx nt
  have oldEq' : Derivation T (.equal (call tag ot)
      (call (tag+1) (call tt ot ::ᵥ call ta ot ::ᵥ call tb ot ::ᵥ nil))) := oldEq
  have newEq' : Derivation T (.equal (call tag nt)
      (call (tag+1) (call tt nt ::ᵥ call ta nt ::ᵥ call tb nt ::ᵥ nil))) := newEq
  obtain ⟨tr⟩ := selectTransport p (tag+1) hsel (call tt ot) (call ta ot) (call tb ot) (call ta nt) (call tb nt)
  have step := Derivation.mp (Derivation.mp tr ay) bn
  let E := accepts (call tag ot)
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have oldAccept := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ oldEq')) he
  have selected := Hilbert.Local.mp (.base step) oldAccept
  have changed := HistoryDecoder.SelectGraphProof.testCongruence (G := [E]) (tag+1)
    (call tt nt) (call tt ot) (call ta nt) (call tb nt) (.base testeq)
  have out := localTrans _ _ _ (.base newEq') (localTrans _ _ _ changed selected)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge out)⟩

theorem conjunctionPreserves {a b : Program 4} (ha : Independent a) (hb : Preserves b) :
    Preserves (conjunction a b) := choosePreserves ha (independentPreserves (constantIndependent 0)) hb

theorem ruleSelectPreserves (r : Nat) {a b : Program 4} (ha : Preserves a) (hb : Preserves b) :
    Preserves (ruleSelect r a b) := choosePreserves (ruleTestIndependent r) hb ha
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.PreservationProof
