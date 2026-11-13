module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingImageProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations
open GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport HistoryKernel
open HistoryIteratorSuffix.WitnessProof RemainingEquationsProof

def imageEquation {ctx : Nat} (tag dtag ttag ptag : Nat) (option lines index fuel : Term ctx) : Formula ctx :=
  .equal (decoded dtag (kernelCall tag (pairCall ptag option lines) index fuel)) (decoded ttag lines)

theorem substImage {m n : Nat} (sub : Fin m → Term n) tag dtag ttag ptag (option lines index fuel : Term m) :
    substituteFormula sub (imageEquation tag dtag ttag ptag option lines index fuel) =
      imageEquation tag dtag ttag ptag (substitute sub option) (substitute sub lines) (substitute sub index) (substitute sub fuel) := by
  simp only [imageEquation,decoded,kernelCall,substituteFormula,substPair,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil]
theorem imageAt {ctx : Nat} tag dtag ttag ptag (option lines index fuel : Term ctx) :
    GorbowStandardInstances.instantiate
      (imageEquation tag dtag ttag ptag (liftTerm option) (.var 0) (liftTerm index) (liftTerm fuel)) lines =
      imageEquation tag dtag ttag ptag option lines index fuel := by
  simp only [GorbowStandardInstances.instantiate,substImage,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
theorem weakenImage {ctx : Nat} tag dtag ttag ptag (option lines index fuel : Term ctx) :
    GorbowPACore.weaken (imageEquation tag dtag ttag ptag option lines index fuel) =
      imageEquation tag dtag ttag ptag (liftTerm option) (liftTerm lines) (liftTerm index) (liftTerm fuel) := by
  rw [GorbowPACore.weaken,substImage]
  rfl
noncomputable def lineTransport {T : Sentence → Prop} {ctx : Nat} tag dtag ttag ptag (option index fuel a b : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (imageEquation tag dtag ttag ptag option a index fuel)
      (imageEquation tag dtag ttag ptag option b index fuel))) := by
  have he := Derivation.logical (A := T) (.equalityReplace
    (imageEquation tag dtag ttag ptag (liftTerm option) (.var 0) (liftTerm index) (liftTerm fuel)) a b)
  rwa [GorbowPACore.logicalFormula,imageAt,imageAt] at he

theorem consImage {n ctx : Nat} (p : Program n) (tag dtag ttag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (htt : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option line rest index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (imageEquation tag dtag ttag ptag option (HistoryLookup.consCall ctag line rest) index fuel)) := by
  obtain ⟨he⟩ := RemainingEquationsProof.kernelCons p tag dtag ptag ctag v l a x ht hd hp hc option line rest index fuel
  obtain ⟨hr⟩ := HistoryLookup.DestructorProof.internalTailCons n p ttag ctag htt hc ctx line rest
  exact ⟨Logic.trans _ _ _ he (Support.equalitySymmetry _ _ hr)⟩

theorem positiveImage {n ctx : Nat} (p : Program n) (tag dtag ttag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (htt : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option code index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (imageEquation tag dtag ttag ptag option (.succ code) index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  let Q := imageEquation tag dtag ttag ptag option (.succ code) index fuel
  let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall cp A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
  have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
  obtain ⟨hi⟩ := consImage p tag dtag ttag ptag ctag v l a x ht hd htt hp hc
    (liftTerm (liftTerm option)) A B (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
  have hout : Hilbert.Local T (ctx+2) [H]
      (imageEquation tag dtag ttag ptag (liftTerm (liftTerm option)) (.succ C)
        (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))) :=
    .mp (.mp (.base (lineTransport tag dtag ttag ptag _ _ _ _ _)) hcons) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenImage,liftTerm,renameTerm,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
  obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
  exact ⟨.mp helim hs⟩

theorem allImage {n ctx : Nat} (p : Program n) (tag dtag ttag ptag ctag : Nat) (v l a : Program 1) (x : Program 3)
    (ht : (nodes p)[tag]? = some ⟨3,kernel v l a x⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (htt : (nodes p)[ttag]? = some ⟨1,HistoryLookup.tail⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option lines index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (imageEquation tag dtag ttag ptag option lines index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := imageEquation tag dtag ttag ptag option lines index fuel
  let E := Formula.equal lines .zero
  obtain ⟨hz⟩ := RemainingEquationsProof.kernelNil p tag dtag ptag v l a x ht hd hp option index fuel
  obtain ⟨htz⟩ := HistoryLookup.DestructorProof.destructorZero (ctx := ctx) p ttag true htt
  have hn : Derivation T (imageEquation tag dtag ttag ptag option .zero index fuel) :=
    Logic.trans _ _ _ hz (Support.equalitySymmetry _ _ htz)
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hzero : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (lineTransport tag dtag ttag ptag option index fuel .zero lines))
      (HistoryOrder.StepProof.localSym _ _ he)) (.base hn)))
  let H := HistoryOrder.SupportProof.predBody lines
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm lines) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hp'⟩ := positiveImage p tag dtag ttag ptag ctag v l a x ht hd htt hp hc
    (liftTerm option) (.var (0 : Fin (ctx+1))) (liftTerm index) (liftTerm fuel)
  have hout : Hilbert.Local T (ctx+1) [H]
      (imageEquation tag dtag ttag ptag (liftTerm option) (liftTerm lines) (liftTerm index) (liftTerm fuel)) :=
    .mp (.mp (.base (lineTransport tag dtag ttag ptag _ _ _ _ _))
      (HistoryOrder.StepProof.localSym _ _ hh)) (.base hp')
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenImage] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hs⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T lines
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzero) hpos) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorDrain.RemainingImageProof
