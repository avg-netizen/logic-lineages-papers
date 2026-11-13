module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.ReferenceCasesProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.EquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph

theorem applyProjectionPair {n arity ctx : Nat} (p : Program n) tag (f : Program 2) (i j : Fin arity)
    (ht : (nodes p)[tag]? = some ⟨arity,applyTwo f (.projection i) (.projection j)⟩)
    (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call tag args) (call (tag+1) (args.get i ::ᵥ args.get j ::ᵥ nil)))) := by
  let g : Fin 2 → Program arity := Fin.cases (.projection i) (Fin.cases (.projection j) Fin.elim0)
  apply HistoryAppend.ValueEquationsProof.binaryValues p tag f g ht args (args.get i) (args.get j)
  · exact SixSol20261112.Fuel.Equations.projection p _ i
      (SixSol20261112.Fuel.Equations.argumentChild p tag f g ht 0) args
  · exact SixSol20261112.Fuel.Equations.projection p _ j
      (SixSol20261112.Fuel.Equations.argumentChild p tag f g ht 1) args

def mpLeftTag (tag : Nat) := tag + argumentTag mpBody mpArguments 2 + 1
def mpRightTag (tag : Nat) := tag + argumentTag mpBody mpArguments 3 + 1
def generalizeLookupTag (tag : Nat) := tag + argumentTag generalizeBody generalizeArguments 2 + 1

theorem mpNodes {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨5,mpCheck⟩) :
    (nodes p)[tag+1]? = some ⟨4,mpBody⟩ ∧
    (nodes p)[mpLeftTag tag]? = some ⟨2,HistoryLookup.lookup⟩ ∧
    (nodes p)[mpRightTag tag]? = some ⟨2,HistoryLookup.lookup⟩ := by
  exact ⟨SixSol20261112.Fuel.Equations.functionChild p tag mpBody mpArguments ht,
    SixSol20261112.Fuel.Equations.functionChild p _ HistoryLookup.lookup _
      (SixSol20261112.Fuel.Equations.argumentChild p tag mpBody mpArguments ht 2),
    SixSol20261112.Fuel.Equations.functionChild p _ HistoryLookup.lookup _
      (SixSol20261112.Fuel.Equations.argumentChild p tag mpBody mpArguments ht 3)⟩

theorem generalizeNodes {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨4,generalizeCheck⟩) :
    (nodes p)[tag+1]? = some ⟨3,generalizeBody⟩ ∧
    (nodes p)[generalizeLookupTag tag]? = some ⟨2,HistoryLookup.lookup⟩ := by
  exact ⟨SixSol20261112.Fuel.Equations.functionChild p tag generalizeBody generalizeArguments ht,
    SixSol20261112.Fuel.Equations.functionChild p _ HistoryLookup.lookup _
      (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeBody generalizeArguments ht 2)⟩

theorem mpEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨5,mpCheck⟩)
    (h context raw r1 r2 : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (mpCall tag h context raw r1 r2) (call (tag+1)
        (context ::ᵥ raw ::ᵥ HistoryLookup.lookupCall (mpLeftTag tag) r1 h ::ᵥ
          HistoryLookup.lookupCall (mpRightTag tag) r2 h ::ᵥ nil)))) := by
  let args := h ::ᵥ context ::ᵥ raw ::ᵥ r1 ::ᵥ r2 ::ᵥ nil
  apply SixSol20261112.Fuel.Equations.compositionValues p tag mpBody mpArguments ht args
  intro i
  cases i using Fin.cases with
  | zero => exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 5)
      (SixSol20261112.Fuel.Equations.argumentChild p tag mpBody mpArguments ht 0) args
  | succ i => cases i using Fin.cases with
    | zero => exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 5)
        (SixSol20261112.Fuel.Equations.argumentChild p tag mpBody mpArguments ht 1) args
    | succ i => cases i using Fin.cases with
      | zero => exact applyProjectionPair p _ HistoryLookup.lookup (3 : Fin 5) 0
          (SixSol20261112.Fuel.Equations.argumentChild p tag mpBody mpArguments ht 2) args
      | succ i => cases i using Fin.cases with
        | zero => exact applyProjectionPair p _ HistoryLookup.lookup (4 : Fin 5) 0
            (SixSol20261112.Fuel.Equations.argumentChild p tag mpBody mpArguments ht 3) args
        | succ i => exact Fin.elim0 i

theorem generalizeEquation {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨4,generalizeCheck⟩) (h context raw r : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (generalizeCall tag h context raw r) (call (tag+1)
        (context ::ᵥ raw ::ᵥ HistoryLookup.lookupCall (generalizeLookupTag tag) r h ::ᵥ nil)))) := by
  let args := h ::ᵥ context ::ᵥ raw ::ᵥ r ::ᵥ nil
  apply SixSol20261112.Fuel.Equations.compositionValues p tag generalizeBody generalizeArguments ht args
  intro i
  cases i using Fin.cases with
  | zero => exact SixSol20261112.Fuel.Equations.projection p _ (1 : Fin 4)
      (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeBody generalizeArguments ht 0) args
  | succ i => cases i using Fin.cases with
    | zero => exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 4)
        (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeBody generalizeArguments ht 1) args
    | succ i => cases i using Fin.cases with
      | zero => exact applyProjectionPair p _ HistoryLookup.lookup (3 : Fin 4) 0
          (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeBody generalizeArguments ht 2) args
      | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.EquationsProof
