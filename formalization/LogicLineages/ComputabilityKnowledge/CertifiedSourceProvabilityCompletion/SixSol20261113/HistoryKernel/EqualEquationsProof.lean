module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualEquationsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

def backward : Program 2 := applyTwo HistoryCodec.difference (.projection 1) (.projection 0)
def inside : Program 2 := choose backward (constant 2 1) (constant 2 0)
def outerArgs : Fin 3 → Program 2 := Fin.cases HistoryCodec.difference (Fin.cases inside (Fin.cases (constant 2 0) Fin.elim0))
def insideArgs : Fin 3 → Program 2 := Fin.cases backward (Fin.cases (constant 2 1) (Fin.cases (constant 2 0) Fin.elim0))
def forwardTag (tag : Nat) := tag+argumentTag HistoryCodec.select outerArgs 0
def insideTag (tag : Nat) := tag+argumentTag HistoryCodec.select outerArgs 1
def backwardTag (tag : Nat) := insideTag tag+argumentTag HistoryCodec.select insideArgs 0+1

def innerValue {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx :=
  call (insideTag tag+1) (pairCall (backwardTag tag) b a ::ᵥ .succ .zero ::ᵥ .zero ::ᵥ nil)
def normal {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx :=
  call (tag+1) (pairCall (forwardTag tag) a b ::ᵥ innerValue tag a b ::ᵥ .zero ::ᵥ nil)

theorem oneEquation {n arity ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨arity,constant arity 1⟩) (args : List.Vector (Term ctx) arity) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (call tag args) (.succ .zero))) := by
  have hz := SixSol20261112.Fuel.Equations.argumentChild p tag .succ (fun _ : Fin 1 => constant arity 0) ht 0
  have hs := SixSol20261112.Fuel.Equations.functionChild p tag .succ (fun _ : Fin 1 => constant arity 0) ht
  obtain ⟨hc⟩ := HistoryAppend.ValueEquationsProof.unaryValues p tag .succ (fun _ : Fin 1 => constant arity 0) ht args .zero
    (HistoryAppend.TableEquationsProof.zeroEquation p _ hz args)
  obtain ⟨he⟩ := Support.intoRegistry p .succ (tag+1) hs _ (NamedArithmeticGraph.Equations.successor (tag+1) ctx (.zero ::ᵥ nil))
  exact ⟨Logic.trans _ _ _ hc he⟩

theorem nodesInstalled {n : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,equalCode⟩) :
    (nodes p)[tag+1]? = some ⟨3,HistoryCodec.select⟩ ∧
    (nodes p)[insideTag tag+1]? = some ⟨3,HistoryCodec.select⟩ ∧
    (nodes p)[forwardTag tag]? = some ⟨2,HistoryCodec.difference⟩ ∧
    (nodes p)[backwardTag tag]? = some ⟨2,HistoryCodec.difference⟩ := by
  have hi := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select outerArgs ht 1
  have hb := SixSol20261112.Fuel.Equations.argumentChild p (insideTag tag) HistoryCodec.select insideArgs hi 0
  exact ⟨SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select outerArgs ht,
    SixSol20261112.Fuel.Equations.functionChild p (insideTag tag) HistoryCodec.select insideArgs hi,
    SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select outerArgs ht 0,
    SixSol20261112.Fuel.Equations.functionChild p _ HistoryCodec.difference _ hb⟩

theorem innerEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,equalCode⟩)
    (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (pairCall (insideTag tag) a b) (innerValue tag a b))) := by
  have hi := SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select outerArgs ht 1
  apply SixSol20261112.Fuel.Equations.compositionValues p (insideTag tag) HistoryCodec.select insideArgs hi
    (a ::ᵥ b ::ᵥ nil) (pairCall (backwardTag tag) b a ::ᵥ .succ .zero ::ᵥ .zero ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero =>
      exact HistoryRuleSuffix.EquationsProof.applyProjectionPair p _ HistoryCodec.difference (1 : Fin 2) 0
        (SixSol20261112.Fuel.Equations.argumentChild p (insideTag tag) HistoryCodec.select insideArgs hi 0) _
  | succ i => cases i using Fin.cases with
    | zero =>
        exact oneEquation p _ (SixSol20261112.Fuel.Equations.argumentChild p (insideTag tag) HistoryCodec.select insideArgs hi 1) _
    | succ i => cases i using Fin.cases with
      | zero =>
          exact HistoryAppend.TableEquationsProof.zeroEquation p _
            (SixSol20261112.Fuel.Equations.argumentChild p (insideTag tag) HistoryCodec.select insideArgs hi 2) _
      | succ i => exact Fin.elim0 i

theorem equalEquation {n ctx : Nat} (p : Program n) tag (ht : (nodes p)[tag]? = some ⟨2,equalCode⟩)
    (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (.equal (pairCall tag a b) (normal tag a b))) := by
  apply SixSol20261112.Fuel.Equations.compositionValues p tag HistoryCodec.select outerArgs ht
    (a ::ᵥ b ::ᵥ nil) (pairCall (forwardTag tag) a b ::ᵥ innerValue tag a b ::ᵥ .zero ::ᵥ nil)
  intro i
  cases i using Fin.cases with
  | zero => exact ⟨.logical (.reflexive _)⟩
  | succ i => cases i using Fin.cases with
    | zero => exact innerEquation p tag ht a b
    | succ i => cases i using Fin.cases with
      | zero =>
          exact HistoryAppend.TableEquationsProof.zeroEquation p _
            (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select outerArgs ht 2) _
      | succ i => exact Fin.elim0 i
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryKernel.EqualEquationsProof
