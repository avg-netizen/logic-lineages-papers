module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

def consTag (tag : Nat) := tag+1+1
def stepTagAt (tag : Nat) := tag+stepTag tableBase
def valueTag (tag : Nat) := stepTagAt tag + argumentTag HistoryCodec.cons tableStepArguments 0

def tableCall {ctx : Nat} (tag : Nat) (count right : Term ctx) : Term ctx := call tag (count ::ᵥ right ::ᵥ nil)
def entryCall {ctx : Nat} (tag : Nat) (count previous right : Term ctx) : Term ctx :=
  call (valueTag tag) (count ::ᵥ previous ::ᵥ right ::ᵥ nil)

theorem substTable {m n : Nat} (sub : Fin m → Term n) tag (count right : Term m) :
    substitute sub (tableCall tag count right) = tableCall tag (substitute sub count) (substitute sub right) := by
  simp only [tableCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]

theorem consCopies {n ctx : Nat} (p : Program n) s t
    (hs : (nodes p)[s]? = some ⟨2,HistoryCodec.cons⟩)
    (ht : (nodes p)[t]? = some ⟨2,HistoryCodec.cons⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryLookup.consCall s a b) (HistoryLookup.consCall t a b))) := by
  have hp := SixSol20261112.Fuel.Equations.argumentChild p s .succ (fun _ : Fin 1 => HistoryCodec.pair) hs 0
  have hq := SixSol20261112.Fuel.Equations.argumentChild p t .succ (fun _ : Fin 1 => HistoryCodec.pair) ht 0
  obtain ⟨he⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p _ _ hp hq a b
  obtain ⟨hl⟩ := HistoryCodec.PairProof.internalCons n p s hs ctx a b
  obtain ⟨hr⟩ := HistoryCodec.PairProof.internalCons n p t ht ctx a b
  exact ⟨Logic.trans _ _ _ hl (Logic.trans _ _ _ (Logic.unary (.succ (.var 0)) _ _ he)
    (Support.equalitySymmetry _ _ hr))⟩

theorem baseInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,table⟩) :
    (nodes p)[tag+1]? = some ⟨1,tableBase⟩ :=
  GorbowPRSubtree.Proof.lookupTransport n p tag ⟨2,table⟩ 1 ⟨1,tableBase⟩ ht
    (GorbowPRChildTags.Proof.recursionBase 1 tableBase tableStep)

theorem consInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,table⟩) :
    (nodes p)[consTag tag]? = some ⟨2,HistoryCodec.cons⟩ :=
  SixSol20261112.Fuel.Equations.functionChild p (tag+1) HistoryCodec.cons tableBaseArguments (baseInstalled p tag ht)

theorem stepInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,table⟩) :
    (nodes p)[stepTagAt tag]? = some ⟨3,tableStep⟩ :=
  SixSol20261112.Fuel.Equations.recursionStepChild p tag tableBase tableStep ht

theorem valueInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,table⟩) :
    (nodes p)[valueTag tag]? = some ⟨3,value⟩ :=
  SixSol20261112.Fuel.Equations.argumentChild p (stepTagAt tag) HistoryCodec.cons tableStepArguments (stepInstalled p tag ht) 0

theorem zeroEquation {n arity ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨arity,zeroProgram arity⟩) (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) .zero)) := by
  have hf := SixSol20261112.Fuel.Equations.functionChild p tag .zero Fin.elim0 ht
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag .zero Fin.elim0 ht args nil (fun i => Fin.elim0 i)
  obtain ⟨hz⟩ := Support.intoRegistry p .zero (tag+1) hf _ (NamedArithmeticGraph.Equations.zero (tag+1) ctx)
  exact ⟨Logic.trans _ _ _ hc hz⟩

theorem tableZero {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,table⟩) (right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (tableCall tag .zero right) (HistoryLookup.consCall (consTag tag) right .zero))) := by
  have hb := baseInstalled p tag ht
  have hv : ∀ i : Fin 2, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+1+argumentTag HistoryCodec.cons tableBaseArguments i) (right ::ᵥ nil))
        ((right ::ᵥ .zero ::ᵥ nil).get i))) := by
    intro i
    have hi := SixSol20261112.Fuel.Equations.argumentChild p (tag+1) HistoryCodec.cons tableBaseArguments hb i
    cases i using Fin.cases with
    | zero => exact SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 1) hi _
    | succ i => cases i using Fin.cases with
      | zero => exact zeroEquation p _ hi _
      | succ i => exact Fin.elim0 i
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p (tag+1) HistoryCodec.cons tableBaseArguments hb (right ::ᵥ nil) (right ::ᵥ .zero ::ᵥ nil) hv
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionZeroEquation n p tag 1 tableBase tableStep ht ctx (right ::ᵥ nil)
  exact ⟨Logic.trans _ _ _ hz hc⟩

theorem tableSuccessor {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,table⟩) (count right : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (tableCall tag (.succ count) right)
        (HistoryLookup.consCall (consTag tag) (entryCall tag count (tableCall tag count right) right) (tableCall tag count right)))) := by
  have hs := stepInstalled p tag ht
  have hsc := SixSol20261112.Fuel.Equations.functionChild p (stepTagAt tag) HistoryCodec.cons tableStepArguments hs
  let previous := tableCall tag count right
  let entry := entryCall tag count previous right
  have hv : ∀ i : Fin 2, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (stepTagAt tag+argumentTag HistoryCodec.cons tableStepArguments i) (count ::ᵥ previous ::ᵥ right ::ᵥ nil))
        ((entry ::ᵥ previous ::ᵥ nil).get i))) := by
    intro i
    cases i using Fin.cases with
    | zero => exact ⟨.logical (.reflexive _)⟩
    | succ i => cases i using Fin.cases with
      | zero =>
          have hp := SixSol20261112.Fuel.Equations.argumentChild p (stepTagAt tag) HistoryCodec.cons tableStepArguments hs 1
          exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 3) hp _
      | succ i => exact Fin.elim0 i
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p (stepTagAt tag) HistoryCodec.cons tableStepArguments hs
    (count ::ᵥ previous ::ᵥ right ::ᵥ nil) (entry ::ᵥ previous ::ᵥ nil) hv
  obtain ⟨hz⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p tag 1 tableBase tableStep ht ctx count (right ::ᵥ nil)
  obtain ⟨hcopy⟩ := consCopies p (stepTagAt tag+1) (consTag tag) hsc (consInstalled p tag ht) entry previous
  exact ⟨Logic.trans _ _ _ hz (Logic.trans _ _ _ hc hcopy)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableEquationsProof
