module
public import LogicLineages.PersistentMarking.NumberedWindowNumeralGraphTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof NumberedWindowNumeralGraphTargets
open ID1Completion.InternalTagArithmeticSyntaxProof (OTerm suc z)

private theorem inputsCons {α : Type} {n : Nat} (x : Nat) (v : List.Vector Nat n) :
    inputs (α := α) (x ::ᵥ v) = Fin.cons (numeral x) (inputs v) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [inputs]
  · simp [inputs,List.Vector.get_cons_succ]

private theorem computed {n : Nat} (p : Program n) : ∀ (v : List.Vector Nat n)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)),
    Nonempty (Derivation body Γ (programGraph p (numeral (evaluate p v)) (inputs v))) := by
  induction p with
  | zero =>
    intro xs body α Γ
    exact zeroValue _
  | succ =>
    intro xs body α Γ
    change Nonempty (Derivation _ _ (programGraph .succ (suc (numeral xs.head)) (inputs xs)))
    have h := successorValue (body := body) (Gamma := Γ) (inputs xs)
    simpa only [inputs,List.Vector.get_zero] using h
  | projection i =>
    intro xs body α Γ
    exact projectionValue i _
  | composition p qs hp hqs =>
    intro xs body α Γ
    let ys := List.Vector.ofFn (fun i => evaluate (qs i) xs)
    apply compositionValue p qs _ (inputs xs) (inputs ys) (hp ys body α Γ)
    intro i
    simpa only [inputs,ys,List.Vector.get_ofFn] using hqs i xs body α Γ
  | @recursion n f g hf hg =>
    intro xs body α Γ
    suffices step : ∀ k : Nat, Nonempty (Derivation body Γ
        (programGraph (.recursion f g) (numeral (evaluate (.recursion f g) (k ::ᵥ xs.tail)))
          (inputs (k ::ᵥ xs.tail)))) by
      simpa only [List.Vector.cons_head_tail] using step xs.head
    intro k
    induction k with
    | zero =>
      rw [inputsCons]
      exact recursionZeroValue f g _ (inputs xs.tail) (hf xs.tail body α Γ)
    | succ k ih =>
      let previous := evaluate (.recursion f g) (k ::ᵥ xs.tail)
      let result := evaluate g (k ::ᵥ previous ::ᵥ xs.tail)
      have stepG := hg (k ::ᵥ previous ::ᵥ xs.tail) body α Γ
      rw [inputsCons,inputsCons] at stepG
      rw [inputsCons] at ih ⊢
      exact ID1Completion.InternalRecursionGraphSuccessorIntroductionProof.recursionSuccessorIntroduction Γ
        (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g)
        (numeral result) (numeral k) (numeral previous) (inputs xs.tail) ih stepG

theorem exact_NumeralGraph : NumeralGraph := fun _ p => computed p
#print axioms exact_NumeralGraph
end LogicLineages.PersistentMarking.NumberedWindowNumeralGraphChecks
