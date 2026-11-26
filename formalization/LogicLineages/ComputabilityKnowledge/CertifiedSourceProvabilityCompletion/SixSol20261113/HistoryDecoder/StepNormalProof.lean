module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepEquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepNormalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph StepEquationsProof

def chosen {ctx : Nat} (right : Bool) (a b : Term ctx) : Term ctx := if right then b else a

def choiceArguments (right : Bool) : Fin 3 → Program 5 :=
  Fin.cases backward (Fin.cases (.projection (if right then 0 else 2)) (Fin.cases (.projection 1) Fin.elim0))
def forwardTag (right : Bool) (tag : Nat) := tag + argumentTag HistoryCodec.select (stepArguments right) 0
def choiceTag (right : Bool) (tag : Nat) := tag + argumentTag HistoryCodec.select (stepArguments right) 1
def backwardTag (right : Bool) (tag : Nat) := choiceTag right tag + argumentTag HistoryCodec.select (choiceArguments right) 0
def stepPairTag (right : Bool) (tag : Nat) := forwardPairTag (forwardTag right tag)

theorem choiceEquation {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨5,.composition HistoryCodec.select (choiceArguments right)⟩)
    (b previous a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil))
        (call (tag+1) (call (tag+argumentTag HistoryCodec.select (choiceArguments right) 0)
          (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) ::ᵥ chosen right a b ::ᵥ previous ::ᵥ nil)))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.select (choiceArguments right) ht
    (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil)
    (call (tag+argumentTag HistoryCodec.select (choiceArguments right) 0)
      (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil) ::ᵥ chosen right a b ::ᵥ previous ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨.logical (.reflexive _)⟩
  | succ i => cases i using Fin.cases with
    | zero =>
        have h := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (choiceArguments right) ht 1
        cases right <;> exact SixSol20261112.Fuel.Equations.projection p _ _ h _
    | succ i => cases i using Fin.cases with
      | zero =>
          have h := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (choiceArguments right) ht 2
          exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 5) h _
      | succ i => exact Fin.elim0 i

theorem stepPairInstalled {n : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨5,innerStep right⟩) :
    (nodes p)[stepPairTag right tag]? = some ⟨2,HistoryCodec.pair⟩ := by
  have hf := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 0
  exact forwardPairInstalled p _ hf

/-- Both difference tests are normalized to the SAME actual pair child,
using the proved internal equality of the duplicated literal pair copies. -/
theorem stepEquation {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨5,innerStep right⟩) (b previous a code seed : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil))
        (call (tag+1)
          (call (forwardTag right tag+1) (call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ code ::ᵥ nil) ::ᵥ
            call (choiceTag right tag+1)
              (call (backwardTag right tag+1) (code ::ᵥ call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil) ::ᵥ nil) ::ᵥ
                chosen right a b ::ᵥ previous ::ᵥ nil) ::ᵥ previous ::ᵥ nil)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let args := b ::ᵥ previous ::ᵥ a ::ᵥ code ::ᵥ seed ::ᵥ nil
  let value := call (stepPairTag right tag) (a ::ᵥ b ::ᵥ nil)
  have hf := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 0
  have hc := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 1
  have hb := SixSol20261112.Fuel.Equations.argumentChild p (choiceTag right tag) HistoryCodec.select (choiceArguments right) hc 0
  obtain ⟨hfe⟩ := forwardEquation p (forwardTag right tag) hf b previous a code seed
  obtain ⟨hbe⟩ := backwardEquation p (backwardTag right tag) hb b previous a code seed
  obtain ⟨hce⟩ := choiceEquation p (choiceTag right tag) right hc b previous a code seed
  have hfp := forwardPairInstalled p (forwardTag right tag) hf
  have hbp := backwardPairInstalled p (backwardTag right tag) hb
  obtain ⟨heq⟩ := PairCongruenceProof.pairCopies p _ _ hbp hfp a b
  have hcopy := Logic.unary
    (HistoryDifference.differenceCall (backwardTag right tag+1) (liftTerm code) (.var 0)) _ _ heq
  simp only [HistoryDifference.ShiftProof.substituteDifference,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hcopy
  have hbn := Logic.trans _ _ _ hbe hcopy
  have hchoice := Logic.unary
    (call (choiceTag right tag+1) (.var 0 ::ᵥ liftTerm (chosen right a b) ::ᵥ liftTerm previous ::ᵥ nil)) _ _ hbn
  simp only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] at hchoice
  have hcn := Logic.trans _ _ _ hce hchoice
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.select (stepArguments right) ht args
    (call (forwardTag right tag+1) (value ::ᵥ code ::ᵥ nil) ::ᵥ
      call (choiceTag right tag+1) (call (backwardTag right tag+1) (code ::ᵥ value ::ᵥ nil) ::ᵥ
        chosen right a b ::ᵥ previous ::ᵥ nil) ::ᵥ previous ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨hfe⟩
  | succ i => cases i using Fin.cases with
    | zero => exact ⟨hcn⟩
    | succ i => cases i using Fin.cases with
      | zero =>
          have h := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select (stepArguments right) ht 2
          exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 5) h args
      | succ i => exact Fin.elim0 i

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.StepNormalProof
