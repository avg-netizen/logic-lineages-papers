module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SelectProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SaturationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof SelectProof
open HistoryDecoder.SelectGraphProof (testCongruence)

def template {ctx : Nat} (tag : Nat) (code : Term ctx) : Formula (ctx+1) :=
  .equal (countCall tag (.add (liftTerm code) (.var 0)) (liftTerm code))
    (countCall tag (liftTerm code) (liftTerm code))
theorem templateAt {ctx : Nat} tag (code gap : Term ctx) :
    GorbowStandardInstances.instantiate (template tag code) gap =
      .equal (countCall tag (.add code gap) code) (countCall tag code code) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substCount,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem atCodePlus {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,count⟩) (code gap : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (countCall tag (.add code gap) code) (countCall tag code code))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag code
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi=template tag code from rfl,templateAt]
    exact Hilbert.Local.finish (countCongruence tag _ code code code (.base (.arithmetic (.addZero code))) (.base (.logical (.reflexive code))))
  let C := liftTerm code
  let i : Term (ctx+1) := .var 0
  let B := Term.add C i
  have ih : Hilbert.Local T (ctx+1) [phi] (.equal (countCall tag B C) (countCall tag C C)) := .hypothesis List.mem_cons_self
  obtain ⟨hd,hs⟩ := countNodes p tag ht
  obtain ⟨he⟩ := countSuccessor p tag ht B C
  have hbound : Derivation T (HistoryBounds.weakBound C B) :=
    .mp (HistoryBounds.SupportProof.weakIntro C B i) (.logical (.reflexive B))
  obtain ⟨hdr⟩ := HistoryIteratorDrain.DropInductionProof.internalDropExhaustion n p (dtag tag) hd (ctx+1) B C
  have hz : Derivation T (.equal (HistoryLookup.DropEquationsProof.dropCall (dtag tag) B C) .zero) := .mp hdr hbound
  have hsel := testCongruence (stag tag) _ .zero (countCall tag B C) (.succ (countCall tag B C)) (.base hz)
  obtain ⟨hselect⟩ := HistoryCodec.PairProof.selectZero p (stag tag) hs (countCall tag B C) (.succ (countCall tag B C))
  have hadd := countCongruence tag (.add C (.succ i)) (.succ B) C C
    (.base (.arithmetic (.addSucc C i))) (.base (.logical (.reflexive C)))
  have hout := localTrans _ _ _ hadd (localTrans _ _ _ (.base he)
    (localTrans _ _ _ hsel (localTrans _ _ _ (.base hselect) ih)))
  have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,substCount,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi gap (HistoryCodec.ArithmeticSupport.induction phi hb hstep)
  rw [show phi=template tag code from rfl,templateAt] at h
  exact ⟨h⟩

theorem atLargerBound {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,count⟩) (code bound : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryBounds.weakBound code bound)
        (.equal (countCall tag bound code) (countCall tag code code)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := Formula.equal (countCall tag bound code) (countCall tag code code)
  let H := Formula.equal (liftTerm bound) (.add (liftTerm code) (.var (0 : Fin (ctx+1))))
  have hh : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
  obtain ⟨hs⟩ := atCodePlus p tag ht (liftTerm code) (.var (0 : Fin (ctx+1)))
  have he := countCongruence tag _ _ (liftTerm code) (liftTerm code) hh (.base (.logical (.reflexive _)))
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,GorbowPACore.weaken,substituteFormula,substCount,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ he (.base hs)))
  exact HBQuantifier.existentialElimination T H Q ⟨hb⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SaturationProof
