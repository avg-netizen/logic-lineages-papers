module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.SubstitutionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.LengthZeroProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261113 SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryIteratorSuffix.WitnessProof

def property {ctx : Nat} (ltag : Nat) (code : Term ctx) : Formula ctx :=
 .imp (.equal (HistoryLengthOffset.lengthCall ltag code) .zero) (.equal code .zero)
theorem substProperty {m n : Nat} (s : Fin m → Term n) ltag (code : Term m) :
 substituteFormula s (property ltag code) = property ltag (substitute s code) := by
 simp only [property,substituteFormula,HistoryLengthOffset.lengthCall,Logic.substCall,
  List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenProperty {ctx : Nat} ltag (code : Term ctx) :
 GorbowPACore.weaken (property ltag code) = property ltag (liftTerm code) := by
 rw [GorbowPACore.weaken,substProperty]
 rfl
theorem propertyAt {ctx : Nat} ltag (code : Term ctx) :
 GorbowStandardInstances.instantiate (property ltag (.var (0 : Fin (ctx+1)))) code = property ltag code := by
 simp only [GorbowStandardInstances.instantiate,substProperty,substitute,Fin.cases_zero]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} ltag (a b : Term ctx) :
 Derivation T (.imp (.equal a b) (.imp (property ltag a) (property ltag b))) := by
 have h := Derivation.logical (A := T) (.equalityReplace (property ltag (.var 0)) a b)
 rwa [GorbowPACore.logicalFormula,propertyAt,propertyAt] at h

theorem cons {n ctx : Nat} (p : Program n) (ltag ctag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (head tail : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ltag (HistoryLookup.consCall ctag head tail))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let E := Formula.equal (HistoryLengthOffset.lengthCall ltag (HistoryLookup.consCall ctag head tail)) .zero
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 obtain ⟨hlen⟩ := HistoryLengthOffset.ConsProof.internalLengthCons n p ltag ctag hl hc ctx head tail
 have hbad := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ hlen)) he
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge
  (Hilbert.Local.explosion (.equal (HistoryLookup.consCall ctag head tail) .zero) hbad
   (.base (.arithmetic (.succNotZero (HistoryLengthOffset.lengthCall ltag tail))))))⟩

theorem positive {n ctx : Nat} (p : Program n) (ltag ctag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ltag (.succ code))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let cp := ctag+GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
 have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
 let Q := property ltag (.succ code)
 let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
 let C := liftTerm (liftTerm code)
 let A : Term (ctx+2) := .var 1
 let B : Term (ctx+2) := .var 0
 have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall cp A B) C) := .hypothesis List.mem_cons_self
 obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
 have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
 obtain ⟨hi⟩ := cons p ltag ctag hl hc A B
 have hout := Hilbert.Local.mp (.mp (.base (transport ltag _ _)) hcons) (.base hi)
 have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
  simpa only [Q,C,weakenProperty,liftTerm,renameTerm,substitute,Fin.cases_zero] using
   Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
 obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
 obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
 exact ⟨.mp helim hs⟩

theorem allCodes {n ctx : Nat} (p : Program n) (ltag ctag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (code : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (property ltag code)) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let Q := property ltag code
 let E := Formula.equal code .zero
 have hz : Derivation T (property ltag (.zero : Term ctx)) := Hilbert.lift _ (.logical (.reflexive .zero))
 have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
 have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
  (.mp (.mp (.base (transport ltag .zero code)) (HistoryOrder.StepProof.localSym _ _ he)) (.base hz)))
 let H := HistoryOrder.SupportProof.predBody code
 have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm code) (.succ (.var 0))) := .hypothesis List.mem_cons_self
 obtain ⟨hn⟩ := positive p ltag ctag hl hc (.var (0 : Fin (ctx+1)))
 have hout := Hilbert.Local.mp (.mp (.base (transport ltag _ _)) (HistoryOrder.StepProof.localSym _ _ hh)) (.base hn)
 have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
  simpa only [Q,weakenProperty] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
 obtain ⟨hp⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
 obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T code
 exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hp) hs⟩

/-- Recover the actual empty NEW task stack from the relational endpoint.
This uses the genuine internal length-zero law, not native list decoding. -/
theorem relatedEmpty {n ctx : Nat} (p : Program n) (ltag lookupTag leftTag rightTag ctag : Nat)
 (hl : (nodes p)[ltag]? = some ⟨1,HistoryLengthOffset.lengthProgram⟩)
 (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (tasks : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (stackRelation ltag lookupTag leftTag rightTag .zero tasks) (.equal tasks .zero))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := stackRelation ltag lookupTag leftTag rightTag (.zero : Term ctx) tasks
 have hh : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
 have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) hh
 obtain ⟨hnil⟩ := HistoryLengthOffset.EquationsProof.internalLengthNil n p ltag hl ctx
 have hz := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ he) (.base hnil)
 obtain ⟨hzero⟩ := allCodes p ltag ctag hl hc tasks
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base hzero) hz))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.LengthZeroProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.LengthZeroProof
