module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.OuterFindProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InverseProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof InnerEquationsProof OuterEquationsProof

/-- Existing internal pair-first bound pays outer enumeration coverage. -/
theorem outerComplete {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨2,outer right⟩) (u v : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (outerCall tag (.succ (outerValue right tag u v)) (outerValue right tag u v))
        (chosen right u v))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := outerValue right tag u v
  let Q := Formula.equal (outerCall tag (.succ code) code) (chosen right u v)
  let H := HistoryOrder.upperBody code u
  let U := liftTerm u
  let V := liftTerm v
  let C := outerValue right tag U V
  let x : Term (ctx+1) := .var 0
  have hh : Hilbert.Local T (ctx+1) [H] (.equal C (.add U x)) := by
    have h : Hilbert.Local T (ctx+1) [H] H := .hypothesis List.mem_cons_self
    simpa only [H,code,C,U,V,x,HistoryOrder.upperBody,liftTerm,renameTerm,substValue] using h
  have hsucc := localUnary (.succ (.var 0)) _ _ hh
  have hcount := localTrans _ _ _ hsucc
    (.base (Support.equalitySymmetry _ _ (.arithmetic (.addSucc U x))))
  have hc := localUnary (outerCall tag (.var 0) (liftTerm C)) _ _ hcount
  simp only [substOuter,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hc
  obtain ⟨hfind⟩ := OuterFindProof.outerFind p tag right ht U V x
  have hout := localTrans _ _ _ hc (.base hfind)
  have hbody : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,code,C,U,V,GorbowPACore.weaken,substituteFormula,substOuter,substValue,substChosen,
      substitute,liftTerm,renameTerm] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T H Q ⟨hbody⟩
  have hp := InnerCompleteProof.pairInstalled p (outerInnerTag tag) right (innerInstalled p tag right ht)
  obtain ⟨hbound⟩ := HistoryBounds.PairProof.pairFirstBound n p (innerPairTag right (outerInnerTag tag)) hp ctx u v
  exact ⟨.mp helim hbound⟩

/-- Actual decoder inversion, uniformly in the coordinate selector and all
source terms. No standard-model calibration enters this proof. -/
theorem inverse {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨1,decoder right⟩) (u v : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (call (pairTag right tag) (u ::ᵥ v ::ᵥ nil) ::ᵥ nil)) (chosen right u v))) := by
  have ho := SixSol20261112.Fuel.Equations.functionChild p tag (outer right) decoderArguments ht
  obtain ⟨he⟩ := decoderEquation p tag right ht (call (pairTag right tag) (u ::ᵥ v ::ᵥ nil))
  obtain ⟨hi⟩ := outerComplete p (tag+1) right ho u v
  exact ⟨Logic.trans _ _ _ he hi⟩

theorem internalLeftInverse : Targets.InternalLeftInverse := by
  intro n p tag ht ctx a b
  exact inverse p tag false ht a b

theorem internalRightInverse : Targets.InternalRightInverse := by
  intro n p tag ht ctx a b
  exact inverse p tag true ht a b

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InverseProof
