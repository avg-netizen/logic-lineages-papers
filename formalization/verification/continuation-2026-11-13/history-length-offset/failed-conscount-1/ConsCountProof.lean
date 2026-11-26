module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SelectProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.ConsCountProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof SelectProof
open HistoryLookup.DropEquationsProof (substCons)
open HistoryDecoder.SelectGraphProof (testCongruence)

def template {ctx : Nat} (tag ctag : Nat) (head tail : Term ctx) : Formula (ctx+1) :=
  .equal (countCall tag (.succ (.var 0)) (HistoryLookup.consCall ctag (liftTerm head) (liftTerm tail)))
    (.succ (countCall tag (.var 0) (liftTerm tail)))
theorem templateAt {ctx : Nat} tag ctag (head tail bound : Term ctx) :
    GorbowStandardInstances.instantiate (template tag ctag head tail) bound =
      .equal (countCall tag (.succ bound) (HistoryLookup.consCall ctag head tail)) (.succ (countCall tag bound tail)) := by
  simp only [GorbowStandardInstances.instantiate,template,substituteFormula,substCount,substCons,
    substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem countOne {n ctx : Nat} (p : Program n) tag ctag
    (ht : (nodes p)[tag]? = some ⟨2,count⟩) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (head tail : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (countCall tag (.succ .zero) (HistoryLookup.consCall ctag head tail)) (.succ (countCall tag .zero tail)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := HistoryLookup.consCall ctag head tail
  obtain ⟨hd,hs⟩ := countNodes p tag ht
  obtain ⟨he⟩ := countSuccessor p tag ht .zero code
  obtain ⟨hz⟩ := HistoryLookup.DropEquationsProof.dropZero p (dtag tag) hd code
  obtain ⟨hc0⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx head tail
  let pv := HistoryKernel.pairCall (ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0) head tail
  have hdpos : Derivation T (.equal (HistoryLookup.DropEquationsProof.dropCall (dtag tag) .zero code) (.succ pv)) := Logic.trans _ _ _ hz hc0
  obtain ⟨hsel⟩ := HistoryCodec.PairProof.selectPositive p (stag tag) hs (countCall tag .zero code) (.succ (countCall tag .zero code)) pv
  have he0 := testCongruence (G := []) (stag tag) _ (.succ pv) (countCall tag .zero code) (.succ (countCall tag .zero code)) (.base hdpos)
  obtain ⟨hcZ⟩ := countZero p tag ht code
  obtain ⟨htZ⟩ := countZero p tag ht tail
  have hzeros := localTrans _ _ _ (.base hcZ) (.base (Support.equalitySymmetry _ _ htZ))
  exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base he)
    (localTrans _ _ _ he0 (localTrans _ _ _ (.base hsel) (localUnary (.succ (.var 0)) _ _ hzeros))))⟩

theorem countCons {n ctx : Nat} (p : Program n) tag ctag
    (ht : (nodes p)[tag]? = some ⟨2,count⟩) (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (bound head tail : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (countCall tag (.succ bound) (HistoryLookup.consCall ctag head tail)) (.succ (countCall tag bound tail)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template tag ctag head tail
  obtain ⟨hb0⟩ := countOne p tag ctag ht hc head tail
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,templateAt] using hb0
  let a := liftTerm head
  let b := liftTerm tail
  let i : Term (ctx+1) := .var 0
  let code := HistoryLookup.consCall ctag a b
  let old := countCall tag i b
  have ih : Hilbert.Local T (ctx+1) [phi] (.equal (countCall tag (.succ i) code) (.succ old)) := .hypothesis List.mem_cons_self
  obtain ⟨hd,hs⟩ := countNodes p tag ht
  obtain ⟨hl⟩ := countSuccessor p tag ht (.succ i) code
  obtain ⟨hr⟩ := countSuccessor p tag ht i b
  obtain ⟨hdrop⟩ := HistoryLookup.DropProof.dropCons p (dtag tag) ctag hd hc i a b
  have htest := testCongruence (stag tag) _ _ (countCall tag (.succ i) code) (.succ (countCall tag (.succ i) code)) (.base hdrop)
  have hvalues := selectValues (stag tag) (HistoryLookup.DropEquationsProof.dropCall (dtag tag) i b)
    _ (.succ old) _ (.succ (.succ old)) ih (localUnary (.succ (.var 0)) _ _ ih)
  obtain ⟨hcomm⟩ := selectSuccessor p (stag tag) hs (HistoryLookup.DropEquationsProof.dropCall (dtag tag) i b) old (.succ old)
  have hout := localTrans _ _ _ (.base hl) (localTrans _ _ _ htest (localTrans _ _ _ hvalues
    (localTrans _ _ _ (.base hcomm) (localUnary (.succ (.var 0)) _ _ (.base (Support.equalitySymmetry _ _ hr))))))
  have hstep : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simp only [phi,template,GorbowStandardInduction.successorInstance,substituteFormula,substCount,substCons,
      substitute,successorLift,Fin.cases_zero]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  have h := atTerm phi bound (HistoryCodec.ArithmeticSupport.induction phi hb hstep)
  rw [show phi = template tag ctag head tail from rfl,templateAt] at h
  exact ⟨h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.ConsCountProof
