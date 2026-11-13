module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.InnerCompleteProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.OuterEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph StepNormalProof InnerEquationsProof

def outerStepTag (tag : Nat) := tag + stepTag (zeroProgram 1)
def outerInnerTag (tag : Nat) := outerStepTag tag + 1
def outerCall {ctx : Nat} (tag : Nat) (count code : Term ctx) : Term ctx := call tag (count ::ᵥ code ::ᵥ nil)
def outerValue {ctx : Nat} (right : Bool) (tag : Nat) (u v : Term ctx) : Term ctx := pairValue right (outerInnerTag tag) u v

theorem substOuter {m n : Nat} (sub : Fin m → Term n) tag (count code : Term m) :
    substitute sub (outerCall tag count code) = outerCall tag (substitute sub count) (substitute sub code) := by
  simp only [outerCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil]
theorem substValue {m n : Nat} (sub : Fin m → Term n) right tag (u v : Term m) :
    substitute sub (outerValue right tag u v) = outerValue right tag (substitute sub u) (substitute sub v) := by
  simp only [outerValue,substPair]

theorem innerInstalled {n : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨2,outer right⟩) :
    (nodes p)[outerInnerTag tag]? = some ⟨4,inner right⟩ := by
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag (zeroProgram 1) (outerStep right) ht
  exact SixSol20261112.Fuel.Equations.functionChild p _ (inner right) outerArguments hs

theorem successorProjection {n arity ctx : Nat} (p : Program n) tag (i : Fin arity)
    (ht : (nodes p)[tag]? = some ⟨arity,.composition .succ (fun _ => .projection i)⟩)
    (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (.succ (args.get i)))) := by
  have hs := SixSol20261112.Fuel.Equations.functionChild p tag .succ (fun _ => .projection i) ht
  have hv : ∀ j : Fin 1, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (tag+argumentTag .succ (fun _ => .projection i) j) args) ((args.get i ::ᵥ nil).get j))) := by
    intro j
    cases j using Fin.cases with
    | zero =>
        have hp := SixSol20261112.Fuel.Equations.argumentChild p tag .succ (fun _ => .projection i) ht 0
        exact SixSol20261112.Fuel.Equations.projection p _ i hp args
    | succ j => exact Fin.elim0 j
  obtain ⟨hc⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag .succ (fun _ => .projection i) ht args (args.get i ::ᵥ nil) hv
  obtain ⟨he⟩ := Support.intoRegistry p .succ (tag+1) hs _
    (NamedArithmeticGraph.Equations.successor (tag+1) ctx (args.get i ::ᵥ nil))
  exact ⟨Logic.trans _ _ _ hc he⟩

theorem outerStepEquation {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨3,outerStep right⟩) (count previous code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (count ::ᵥ previous ::ᵥ code ::ᵥ nil))
        (innerCall (tag+1) (.succ code) count code previous))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag (inner right) outerArguments ht
    (count ::ᵥ previous ::ᵥ code ::ᵥ nil) (.succ code ::ᵥ count ::ᵥ code ::ᵥ previous ::ᵥ nil)
  intro i
  have h := SixSol20261112.Fuel.Equations.argumentChild p tag (inner right) outerArguments ht i
  cases i using Fin.cases with
  | zero => exact successorProjection p _ (2 : Fin 3) h _
  | succ i => cases i using Fin.cases with
    | zero => exact SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 3) h _
    | succ i => cases i using Fin.cases with
      | zero => exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 3) h _
      | succ i => cases i using Fin.cases with
        | zero => exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 3) h _
        | succ i => exact Fin.elim0 i

theorem outerSuccessor {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨2,outer right⟩) (count code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (outerCall tag (.succ count) code)
        (innerCall (outerInnerTag tag) (.succ code) count code (outerCall tag count code)))) := by
  obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation
    n p tag 1 (zeroProgram 1) (outerStep right) ht ctx count (code ::ᵥ nil)
  have hs := SixSol20261112.Fuel.Equations.recursionStepChild p tag (zeroProgram 1) (outerStep right) ht
  obtain ⟨he⟩ := outerStepEquation p (outerStepTag tag) right hs count (outerCall tag count code) code
  exact ⟨Logic.trans _ _ _ hr he⟩

theorem decoderEquation {n ctx : Nat} (p : Program n) tag right
    (ht : (nodes p)[tag]? = some ⟨1,decoder right⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag (code ::ᵥ nil)) (outerCall (tag+1) (.succ code) code))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag (outer right) decoderArguments ht
    (code ::ᵥ nil) (.succ code ::ᵥ code ::ᵥ nil)
  intro i
  have h := SixSol20261112.Fuel.Equations.argumentChild p tag (outer right) decoderArguments ht i
  cases i using Fin.cases with
  | zero => exact successorProjection p _ (0 : Fin 1) h _
  | succ i => cases i using Fin.cases with
    | zero => exact SixSol20261112.Fuel.Equations.projection p _ (0 : Fin 1) h _
    | succ i => exact Fin.elim0 i

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDecoder.OuterEquationsProof
