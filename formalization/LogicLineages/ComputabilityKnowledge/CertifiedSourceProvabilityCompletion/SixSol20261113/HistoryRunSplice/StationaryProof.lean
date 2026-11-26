module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.IdleProof

public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.StationaryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel SixSol20261112.HistoryMachine NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryIteratorSuffix.WitnessProof
open HistoryIteratorSuffix.IterationProof (substIteration)

noncomputable def iterationState {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} itag (count a b index fuel : Term ctx)
    (h : Hilbert.Local T ctx G (.equal a b)) :
    Hilbert.Local T ctx G (.equal (iterationCall itag count a index fuel) (iterationCall itag count b index fuel)) := by
  have he := localUnary (iterationCall itag (liftTerm count) (.var 0) (liftTerm index) (liftTerm fuel)) a b h
  simpa only [substIteration,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using he
noncomputable def iterationCount {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)} itag (a b code index fuel : Term ctx)
    (h : Hilbert.Local T ctx G (.equal a b)) :
    Hilbert.Local T ctx G (.equal (iterationCall itag a code index fuel) (iterationCall itag b code index fuel)) := by
  have he := localUnary (iterationCall itag (.var 0) (liftTerm code) (liftTerm index) (liftTerm fuel)) a b h
  simpa only [substIteration,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using he

def stationary {ctx : Nat} (itag dtag : Nat) (count code index fuel : Term ctx) : Formula ctx :=
  .imp (.equal (call dtag (code ::ᵥ nil)) .zero)
    (.equal (iterationCall itag count code index fuel) code)
theorem substStationary {m n : Nat} (sub : Fin m → Term n) itag dtag (count code index fuel : Term m) :
    substituteFormula sub (stationary itag dtag count code index fuel)=
      stationary itag dtag (substitute sub count) (substitute sub code) (substitute sub index) (substitute sub fuel) := by
  simp only [stationary,substituteFormula,substIteration,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute]
theorem weakenStationary {ctx : Nat} itag dtag (count code index fuel : Term ctx) :
    GorbowPACore.weaken (stationary itag dtag count code index fuel)=
      stationary itag dtag (liftTerm count) (liftTerm code) (liftTerm index) (liftTerm fuel) := by
  rw [GorbowPACore.weaken,substStationary]
  rfl
theorem stationaryAt {ctx : Nat} itag dtag (count code index fuel : Term ctx) :
    GorbowStandardInstances.instantiate (stationary itag dtag (liftTerm count) (.var 0) (liftTerm index) (liftTerm fuel)) code =
      stationary itag dtag count code index fuel := by
  simp only [GorbowStandardInstances.instantiate,substStationary,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero]
noncomputable def transport {T : Sentence → Prop} {ctx : Nat} itag dtag (count a b index fuel : Term ctx) :
    Derivation T (.imp (.equal a b) (.imp (stationary itag dtag count a index fuel) (stationary itag dtag count b index fuel))) := by
  have he := Derivation.logical (A := T) (.equalityReplace (stationary itag dtag (liftTerm count) (.var 0) (liftTerm index) (liftTerm fuel)) a b)
  rwa [GorbowPACore.logicalFormula,stationaryAt,stationaryAt] at he

theorem pairStationary {n ctx : Nat} (p : Program n) (itag dtag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (count option lines index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stationary itag dtag count (state ptag option lines) index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let E := Formula.equal (call dtag (state ptag option lines ::ᵥ nil)) .zero
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  obtain ⟨hr⟩ := HistoryLookup.DestructorProof.decoderCrossPair p dtag ptag true hd hp option lines
  have hl := localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ (.base hr)) he
  have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag option lines option .zero (.base (.logical (.reflexive option))) hl
  obtain ⟨hidle⟩ := IdleProof.internalIdle v l a x n p itag ptag hi hp ctx count option index fuel
  have hiter := iterationState itag count _ _ index fuel hs
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hiter
    (localTrans _ _ _ (.base hidle) (HistoryOrder.StepProof.localSym _ _ hs))))⟩

theorem allStationary {n ctx : Nat} (p : Program n) (itag dtag ptag : Nat) (v l a : Program 1) (x : Program 3)
    (hi : (nodes p)[itag]? = some ⟨4,iterator (HistoryKernel.kernel v l a x)⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (count code index fuel : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stationary itag dtag count code index fuel)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := stationary itag dtag count code index fuel
  let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall ptag A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨hs⟩ := pairStationary p itag dtag ptag v l a x hi hd hp (liftTerm (liftTerm count)) A B
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel))
  have hout := Hilbert.Local.mp (.mp (.base (transport itag dtag (liftTerm (liftTerm count)) _ _
    (liftTerm (liftTerm index)) (liftTerm (liftTerm fuel)))) hh) (.base hs)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenStationary] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody ptag code) Q ⟨hinner⟩
  obtain ⟨hsurj⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p ptag hp ctx code
  exact ⟨.mp helim hsurj⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.StationaryProof

#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.StationaryProof
