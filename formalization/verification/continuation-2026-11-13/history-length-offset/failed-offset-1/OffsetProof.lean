module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.OffsetCasesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.OffsetProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport OffsetSupportProof OffsetCasesProof

theorem zeroAll {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (allBounded ltag atag rtag .zero right index)) := by
  obtain ⟨hz⟩ := allCodes p ltag atag rtag ctag hl ha hr hc false (.zero : Term (ctx+1)) (.var 0) (liftTerm right) (liftTerm index)
  exact ⟨.generalize hz⟩

theorem successorAll {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.lookup⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (count right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (allBounded ltag atag rtag count right index) (allBounded ltag atag rtag (.succ count) right index))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let P := allBounded ltag atag rtag count right index
  let Q := bounded ltag atag rtag (.succ (liftTerm count)) (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index)
  obtain ⟨hs⟩ := allCodes p ltag atag rtag ctag hl ha hr hc true (liftTerm count) (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index)
  have hs' : Derivation T (.imp (GorbowPACore.weaken P) Q) := by
    simpa only [P,Q,GorbowPACore.weaken,substAll,liftTerm,renameTerm,phase,if_true] using hs
  have hd := Derivation.mp (.logical (.allDistribute (GorbowPACore.weaken P) Q)) (.generalize hs')
  exact ⟨Hilbert.compose hd (.logical (.allVacuous P))⟩

def template {ctx : Nat} ltag atag rtag (right index : Term ctx) : Formula (ctx+1) :=
  allBounded ltag atag rtag (.var 0) (liftTerm right) (liftTerm index)
theorem templateAt {ctx : Nat} ltag atag rtag (right index count : Term ctx) :
    GorbowStandardInstances.instantiate (template ltag atag rtag right index) count=
      allBounded ltag atag rtag count right index := by
  simp only [GorbowStandardInstances.instantiate,template,substAll,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem internalRightLookupOffset : Targets.InternalRightLookupOffset := by
  intro n p ltag atag rtag ctag hl ha hr hc ctx left right index
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := template ltag atag rtag right index
  obtain ⟨hz⟩ := zeroAll p ltag atag rtag ctag hl ha hr hc right index
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    rw [show phi=template ltag atag rtag right index from rfl,templateAt]
    exact hz
  obtain ⟨hs0⟩ := successorAll p ltag atag rtag ctag hl ha hr hc (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index)
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,template,GorbowStandardInduction.successorInstance,substAll,substitute,successorLift,Fin.cases_zero] using hs0
  have hall := atTerm phi (lengthCall ltag left) (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  rw [show phi=template ltag atag rtag right index from rfl,templateAt] at hall
  exact ⟨.mp (.mp (allElim ltag atag rtag (lengthCall ltag left) left right index) hall) (.logical (.reflexive _))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.OffsetProof
