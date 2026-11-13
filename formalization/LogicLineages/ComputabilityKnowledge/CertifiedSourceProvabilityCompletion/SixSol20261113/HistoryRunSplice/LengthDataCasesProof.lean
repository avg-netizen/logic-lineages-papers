module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open HistoryLengthOffset
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof LengthDataSupportProof
open HistoryIteratorSuffix.WitnessProof

def phase {ctx : Nat} (step : Bool) (ltag atag rtag : Nat) (count left right index : Term ctx) : Formula ctx :=
  if step then .imp (allBounded ltag atag rtag count right index) (bounded ltag atag rtag (.succ count) left right index)
  else bounded ltag atag rtag .zero left right index

theorem substPhase {m n : Nat} (sub : Fin m → Term n) step ltag atag rtag (count left right index : Term m) :
    substituteFormula sub (phase step ltag atag rtag count left right index)=
      phase step ltag atag rtag (substitute sub count) (substitute sub left) (substitute sub right) (substitute sub index) := by
  cases step <;> simp only [phase,Bool.false_eq_true,if_false,if_true,substituteFormula,substAll,substBounded,substitute]
theorem weakenPhase {ctx : Nat} step ltag atag rtag (count left right index : Term ctx) :
    GorbowPACore.weaken (phase step ltag atag rtag count left right index)=
      phase step ltag atag rtag (liftTerm count) (liftTerm left) (liftTerm right) (liftTerm index) := by
  rw [GorbowPACore.weaken,substPhase]
  rfl
theorem phaseAt {ctx : Nat} step ltag atag rtag (count left right index : Term ctx) :
    GorbowStandardInstances.instantiate (phase step ltag atag rtag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index)) left =
      phase step ltag atag rtag count left right index := by
  simp only [GorbowStandardInstances.instantiate,substPhase,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} step ltag atag rtag (count a b right index : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (phase step ltag atag rtag count a right index) (phase step ltag atag rtag count b right index))) := by
  have h := Derivation.logical (A := T) (.equalityReplace
    (phase step ltag atag rtag (liftTerm count) (.var 0) (liftTerm right) (liftTerm index)) a b)
  rwa [GorbowPACore.logicalFormula,phaseAt,phaseAt] at h

theorem consPhase {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (step : Bool) (count head tail right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (phase step ltag atag rtag count (HistoryLookup.consCall ctag head tail) right index)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := HistoryLookup.consCall ctag head tail
  obtain ⟨hlen⟩ := ConsProof.internalLengthCons n p ltag ctag hl hc ctx head tail
  cases step with
  | false =>
      let E := Formula.equal (lengthCall ltag code) .zero
      have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
      have hbad := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hlen)) he
      exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
        (Hilbert.Local.explosion (property ltag atag rtag code right index) hbad
          (.base (.arithmetic (.succNotZero (lengthCall ltag tail))))))⟩
  | true =>
      let P := allBounded ltag atag rtag count right index
      let E := Formula.equal (lengthCall ltag code) (.succ count)
      have he : Hilbert.Local T ctx [E,P] E := .hypothesis List.mem_cons_self
      have ih : Hilbert.Local T ctx [E,P] P := .hypothesis (by simp)
      have hsucc := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hlen)) he
      have ht : Hilbert.Local T ctx [E,P] (.equal (lengthCall ltag tail) count) :=
        .mp (.base (.arithmetic (.succInjective _ _))) hsucc
      have hi := Hilbert.Local.mp (.base (allElim ltag atag rtag count tail right index)) ih
      obtain ⟨hs⟩ := consOffset p ltag atag rtag ctag hl ha hr hc head tail right index
      have hout := Hilbert.Local.mp (.base hs) (.mp hi ht)
      exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩

theorem nilPhase {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (step : Bool) (count right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (phase step ltag atag rtag count .zero right index)) := by
  obtain ⟨hz⟩ := nilOffset p ltag atag rtag hl ha hr right index
  cases step with
  | false => exact ⟨Hilbert.lift _ hz⟩
  | true => exact ⟨Hilbert.lift _ (Hilbert.lift _ hz)⟩

theorem positivePhase {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (step : Bool) (count code right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (phase step ltag atag rtag count (.succ code) right index)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  let Q := phase step ltag atag rtag count (.succ code) right index
  let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall cp A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
  have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
  obtain ⟨hi⟩ := consPhase p ltag atag rtag ctag hl ha hr hc step (liftTerm (liftTerm count)) A B
    (liftTerm (liftTerm right)) (liftTerm (liftTerm index))
  have hout := Hilbert.Local.mp (.mp (.base (transport step ltag atag rtag (liftTerm (liftTerm count)) _ _
    (liftTerm (liftTerm right)) (liftTerm (liftTerm index)))) hcons) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenPhase,liftTerm,renameTerm,substitute,Fin.cases_zero] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
  obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
  exact ⟨.mp helim hs⟩

theorem allCodes {n ctx : Nat} (p : Program n) (ltag atag rtag ctag : Nat)
    (hl : (nodes p)[ltag]? = some ⟨1,lengthProgram⟩)
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hr : (nodes p)[rtag]? = some ⟨2,HistoryLookup.drop⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (step : Bool) (count left right index : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (phase step ltag atag rtag count left right index)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := phase step ltag atag rtag count left right index
  let E := Formula.equal left .zero
  obtain ⟨hz⟩ := nilPhase p ltag atag rtag ctag hl ha hr hc step count right index
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (transport step ltag atag rtag count .zero left right index)) (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
  let H := HistoryOrder.SupportProof.predBody left
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm left) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := positivePhase p ltag atag rtag ctag hl ha hr hc step (liftTerm count) (.var (0 : Fin (ctx+1))) (liftTerm right) (liftTerm index)
  have hout := Hilbert.Local.mp (.mp (.base (transport step ltag atag rtag (liftTerm count) _ _ (liftTerm right) (liftTerm index)))
    (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenPhase] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hp⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T left
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hp) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.LengthDataCasesProof
