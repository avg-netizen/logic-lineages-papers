module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepGraphProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepInvariantProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport StepNormalProof

theorem differenceDiagonal {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.difference⟩) (a : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (HistoryDifference.differenceCall tag a a) .zero)) := by
  obtain ⟨h⟩ := HistoryDifference.ArithmeticProof.differenceCancel n p tag ht ctx a .zero
  have hc := HistoryDifference.ShiftProof.congruentSecond tag (.add a .zero) a a
    (Derivation.arithmetic (A := GorbowPRNumeralCalculation.Theory p) (.addZero a))
  exact ⟨Logic.trans _ _ _ (Support.equalitySymmetry _ _ hc) h⟩

theorem stepHit {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨5,innerStep right⟩) (a b previous seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ seed ::ᵥ nil))
        (chosen right a b))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil)
  let y := chosen right a b
  let t1 := call (forwardTag right tag+1) (code ::ᵥ code ::ᵥ nil)
  let t2 := call (backwardTag right tag+1) (code ::ᵥ code ::ᵥ nil)
  let inside := call (choiceTag right tag+1) (t2 ::ᵥ y ::ᵥ previous ::ᵥ nil)
  have hso := SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select (stepArguments right) ht
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 1
  have hsi := SixSol20261112.Fuel.Equations.functionChild p (choiceTag right tag) HistoryCodec.select (choiceArguments right) hc
  have hf := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 0
  have hdf := SixSol20261112.Fuel.Equations.functionChild p (forwardTag right tag) HistoryCodec.difference forwardArguments hf
  have hb := SixSol20261112.Fuel.Equations.argumentChild p (choiceTag right tag) HistoryCodec.select (choiceArguments right) hc 0
  have hdb := SixSol20261112.Fuel.Equations.functionChild p (backwardTag right tag) HistoryCodec.difference backwardArguments hb
  obtain ⟨hn⟩ := stepEquation p tag right ht b previous a code seed
  obtain ⟨hz1⟩ := differenceDiagonal p (forwardTag right tag+1) hdf code
  obtain ⟨hz2⟩ := differenceDiagonal p (backwardTag right tag+1) hdb code
  obtain ⟨hzo⟩ := HistoryCodec.PairProof.selectZero p (tag+1) hso inside previous
  obtain ⟨hzi⟩ := HistoryCodec.PairProof.selectZero p (choiceTag right tag+1) hsi y previous
  have hco := Logic.unary (call (tag+1) (.var 0 ::ᵥ liftTerm inside ::ᵥ liftTerm previous ::ᵥ nil)) _ _ hz1
  have hci := Logic.unary (call (choiceTag right tag+1) (.var 0 ::ᵥ liftTerm y ::ᵥ liftTerm previous ::ᵥ nil)) _ _ hz2
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hco hci
  exact ⟨Logic.trans _ _ _ hn (Logic.trans _ _ _ hco (Logic.trans _ _ _ hzo (Logic.trans _ _ _ hci hzi)))⟩

theorem stepPreserve {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨5,innerStep right⟩) (a b u v seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ chosen right u v ::ᵥ a ::ᵥ call (stepPairTag right tag) (u ::ᵥ v ::ᵥ nil) ::ᵥ seed ::ᵥ nil))
        (chosen right u v))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let code := call (stepPairTag right tag) (u ::ᵥ v ::ᵥ nil)
  let output := call tag (b ::ᵥ chosen right u v ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)
  let target := chosen right u v
  let Q := Formula.equal output target
  let H := Formula.conj (.equal (call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil)) code)
    (.equal output (chosen right a b))
  have hp := stepPairInstalled p tag right ht
  obtain ⟨hgraph⟩ := StepGraphProof.stepGraph p tag right ht b target a code seed
  obtain ⟨hinj⟩ := HistoryCancellation.InjectivityProof.pairInjective n p (stepPairTag right tag) hp ctx a b u v
  have hright : Derivation T (.imp H Q) := by
    have h : Hilbert.Local T ctx [H] H := .hypothesis List.mem_cons_self
    have he := Hilbert.Local.mp (.base (.logical (.andLeft _ _))) h
    have hv := Hilbert.Local.mp (.base (.logical (.andRight _ _))) h
    have hc := Hilbert.Local.mp (.base hinj) he
    have htgt : Hilbert.Local T ctx [H] (.equal (chosen right a b) target) := by
      cases right with
      | false => exact .mp (.base (.logical (.andLeft _ _))) hc
      | true => exact .mp (.base (.logical (.andRight _ _))) hc
    exact Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hv htgt))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) (Hilbert.identity Q)) hright) hgraph⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepInvariantProof
