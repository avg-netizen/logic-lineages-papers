module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.IndependenceProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.SelectProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def accepts {ctx : Nat} (v : Term ctx) : Formula ctx := .equal v (.succ .zero)
def transport {ctx : Nat} (tag : Nat) (test a b a' b' : Term ctx) : Formula ctx :=
  .imp (.imp (accepts a) (accepts a')) (.imp (.imp (accepts b) (accepts b'))
    (.imp (accepts (call tag (test ::ᵥ a ::ᵥ b ::ᵥ nil)))
      (accepts (call tag (test ::ᵥ a' ::ᵥ b' ::ᵥ nil)))))

theorem substituteTransport {m n : Nat} (s : Fin m → Term n) tag (test a b a' b' : Term m) :
    substituteFormula s (transport tag test a b a' b') =
      transport tag (substitute s test) (substitute s a) (substitute s b) (substitute s a') (substitute s b') := by
  simp only [transport,accepts,substituteFormula,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem zeroTransport {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (a b a' b' : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (transport tag .zero a b a' b')) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let A := Formula.imp (accepts a) (accepts a')
  let B := Formula.imp (accepts b) (accepts b')
  let E := accepts (call tag (.zero ::ᵥ a ::ᵥ b ::ᵥ nil))
  obtain ⟨old⟩ := HistoryCodec.PairProof.selectZero p tag ht a b
  obtain ⟨new⟩ := HistoryCodec.PairProof.selectZero p tag ht a' b'
  have he : Hilbert.Local T ctx [E,B,A] E := .hypothesis List.mem_cons_self
  have ha : Hilbert.Local T ctx [E,B,A] A := .hypothesis (by simp)
  have harg := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
  have hout := localTrans _ _ _ (.base new) (.mp ha harg)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem successorTransport {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (k a b a' b' : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (transport tag (.succ k) a b a' b')) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let A := Formula.imp (accepts a) (accepts a')
  let B := Formula.imp (accepts b) (accepts b')
  let E := accepts (call tag (.succ k ::ᵥ a ::ᵥ b ::ᵥ nil))
  obtain ⟨old⟩ := HistoryCodec.PairProof.selectPositive p tag ht a b k
  obtain ⟨new⟩ := HistoryCodec.PairProof.selectPositive p tag ht a' b' k
  have he : Hilbert.Local T ctx [E,B,A] E := .hypothesis List.mem_cons_self
  have hb : Hilbert.Local T ctx [E,B,A] B := .hypothesis (by simp)
  have harg := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
  have hout := localTrans _ _ _ (.base new) (.mp hb harg)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge (Hilbert.Local.discharge hout)))⟩

theorem selectTransport {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨3,HistoryCodec.select⟩) (test a b a' b' : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (transport tag test a b a' b')) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := transport tag (.var 0) (liftTerm a) (liftTerm b) (liftTerm a') (liftTerm b')
  obtain ⟨hz⟩ := zeroTransport p tag ht a b a' b'
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,GorbowStandardInstances.instantiate,substituteTransport,substitute,
      liftTerm,Support.shiftCancel,Fin.cases_zero] using hz
  obtain ⟨hs⟩ := successorTransport p tag ht (.var (0 : Fin (ctx+1))) (liftTerm a) (liftTerm b) (liftTerm a') (liftTerm b')
  have step : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    apply Hilbert.lift phi
    simpa only [phi,GorbowStandardInduction.successorInstance,substituteTransport,substitute,
      successorLift,Fin.cases_zero] using hs
  have hall := induction phi hb step
  have hout := atTerm phi test hall
  exact ⟨by simpa only [phi,GorbowStandardInstances.instantiate,substituteTransport,substitute,
    liftTerm,Support.shiftCancel,Fin.cases_zero] using hout⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.SelectProof
