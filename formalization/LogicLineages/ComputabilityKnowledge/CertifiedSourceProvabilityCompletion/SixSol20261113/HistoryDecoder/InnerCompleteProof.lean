module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerFindProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerCompleteProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof InnerEquationsProof

theorem pairInstalled {n : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) :
    (nodes p)[innerPairTag right tag]? = some ⟨2,HistoryCodec.pair⟩ :=
  stepPairInstalled p (innerStepTag tag) right (stepInstalled p tag right ht)

/-- The actual pair bound discharges the scan-coverage gap: the complete
inclusive inner scan finds the target from any seed. -/
theorem innerComplete {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨4,inner right⟩) (u v seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (innerCall tag (.succ (pairValue right tag u v)) u (pairValue right tag u v) seed)
        (chosen right u v))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := pairValue right tag u v
  let Q := Formula.equal (innerCall tag (.succ code) u code seed) (chosen right u v)
  let H := HistoryOrder.upperBody code v
  let U := liftTerm u
  let V := liftTerm v
  let S := liftTerm seed
  let C := pairValue right tag U V
  let x : Term (ctx+1) := .var 0
  have hh : Hilbert.Local T (ctx+1) [H] (.equal C (.add V x)) := by
    have h : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
    simpa only [H,code,C,U,V,x,HistoryOrder.upperBody,liftTerm,renameTerm,substPair] using h
  have hsucc := localUnary (.succ (.var 0)) _ _ hh
  have hcount := localTrans _ _ _ hsucc
    (.base (Support.equalitySymmetry _ _ (.arithmetic (.addSucc V x))))
  have hc := localUnary (innerCall tag (.var 0) (liftTerm U) (liftTerm C) (liftTerm S)) _ _ hcount
  simp only [substInner,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hc
  obtain ⟨hfind⟩ := InnerFindProof.innerFind p tag right ht U V S x
  have hout := localTrans _ _ _ hc (.base hfind)
  have hbody : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,code,C,U,V,S,GorbowPACore.weaken,substituteFormula,substInner,substPair,substChosen,
      substitute,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T H Q ⟨hbody⟩
  obtain ⟨hbound⟩ := HistoryBounds.PairProof.pairSecondBound n p (innerPairTag right tag)
    (pairInstalled p tag right ht) ctx u v
  exact ⟨.mp helim hbound⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerCompleteProof
