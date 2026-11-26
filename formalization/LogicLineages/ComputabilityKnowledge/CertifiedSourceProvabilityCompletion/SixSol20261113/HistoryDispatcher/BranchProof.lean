module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.PreservationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.BranchProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open HistoryRuleSuffix IndependenceProof SelectProof PreservationProof

theorem mpPreserves : Preserves (.composition mpCheck mpArguments) := by
  intro arity p tag atag ht ha ctx index fuel h tail line
  let T := GorbowPRNumeralCalculation.Theory p
  let ot := args index fuel h line
  let nt := args index fuel (HistoryAppend.appendCall atag h tail) line
  let child (i : Fin 5) := tag+argumentTag mpCheck mpArguments i
  let oldValues := h ::ᵥ call (child 1) ot ::ᵥ call (child 2) ot ::ᵥ call (child 3) ot ::ᵥ call (child 4) ot ::ᵥ nil
  let newValues := (HistoryAppend.appendCall atag h tail) ::ᵥ call (child 1) nt ::ᵥ call (child 2) nt ::ᵥ call (child 3) nt ::ᵥ call (child 4) nt ::ᵥ nil
  let mixedValues := (HistoryAppend.appendCall atag h tail) ::ᵥ call (child 1) ot ::ᵥ call (child 2) ot ::ᵥ call (child 3) ot ::ᵥ call (child 4) ot ::ᵥ nil
  have hf := SixSol20261112.Fuel.Equations.functionChild p tag mpCheck mpArguments ht
  have values (history : Term ctx) : ∀ i : Fin 5,
      Nonempty (Derivation T (.equal (call (child i) (args index fuel history line))
        ((history ::ᵥ call (child 1) (args index fuel history line) ::ᵥ call (child 2) (args index fuel history line) ::ᵥ call (child 3) (args index fuel history line) ::ᵥ call (child 4) (args index fuel history line) ::ᵥ nil).get i))) := by
    intro i
    cases i using Fin.cases with
    | zero =>
      exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 4) (SixSol20261112.Fuel.Equations.argumentChild p tag mpCheck mpArguments ht 0) _
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        exact ⟨.logical (.reflexive _)⟩
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          exact ⟨.logical (.reflexive _)⟩
        | succ i =>
          cases i using Fin.cases with
          | zero =>
            exact ⟨.logical (.reflexive _)⟩
          | succ i =>
            cases i using Fin.cases with
            | zero =>
              exact ⟨.logical (.reflexive _)⟩
            | succ i =>
              exact Fin.elim0 i
  obtain ⟨oldEq⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag mpCheck mpArguments ht ot oldValues (values h)
  obtain ⟨newEq⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag mpCheck mpArguments ht nt newValues (values (HistoryAppend.appendCall atag h tail))
  have hc : Derivation T (.equal (call (tag+1) newValues) (call (tag+1) mixedValues)) := by
    apply Logic.callCongruence T (tag+1) newValues mixedValues
    intro i
    cases i using Fin.cases with
    | zero =>
      exact .logical (.reflexive _)
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        exact Classical.choice (independentEquation contextIndependent arity p (child 1)
          (SixSol20261112.Fuel.Equations.argumentChild p tag mpCheck mpArguments ht 1)
          ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          exact Classical.choice (independentEquation rawIndependent arity p (child 2)
            (SixSol20261112.Fuel.Equations.argumentChild p tag mpCheck mpArguments ht 2)
            ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
        | succ i =>
          cases i using Fin.cases with
          | zero =>
            exact Classical.choice (independentEquation ref1Independent arity p (child 3)
              (SixSol20261112.Fuel.Equations.argumentChild p tag mpCheck mpArguments ht 3)
              ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
          | succ i =>
            cases i using Fin.cases with
            | zero =>
              exact Classical.choice (independentEquation ref2Independent arity p (child 4)
                (SixSol20261112.Fuel.Equations.argumentChild p tag mpCheck mpArguments ht 4)
                ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
            | succ i =>
              exact Fin.elim0 i
  obtain ⟨hs⟩ := HistoryRuleSuffix.SuffixProof.internalMPSuffix arity p (tag+1) atag hf ha ctx h tail
    (call (child 1) ot) (call (child 2) ot) (call (child 3) ot) (call (child 4) ot)
  let E := accepts (call tag ot)
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have coreOld := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ oldEq)) he
  have coreNew := Hilbert.Local.mp (.base hs) coreOld
  have out := localTrans _ _ _ (.base newEq) (localTrans _ _ _ (.base hc) coreNew)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge out)⟩

theorem generalizePreserves : Preserves (.composition generalizeCheck generalizeArguments) := by
  intro arity p tag atag ht ha ctx index fuel h tail line
  let T := GorbowPRNumeralCalculation.Theory p
  let ot := args index fuel h line
  let nt := args index fuel (HistoryAppend.appendCall atag h tail) line
  let child (i : Fin 4) := tag+argumentTag generalizeCheck generalizeArguments i
  let oldValues := h ::ᵥ call (child 1) ot ::ᵥ call (child 2) ot ::ᵥ call (child 3) ot ::ᵥ nil
  let newValues := (HistoryAppend.appendCall atag h tail) ::ᵥ call (child 1) nt ::ᵥ call (child 2) nt ::ᵥ call (child 3) nt ::ᵥ nil
  let mixedValues := (HistoryAppend.appendCall atag h tail) ::ᵥ call (child 1) ot ::ᵥ call (child 2) ot ::ᵥ call (child 3) ot ::ᵥ nil
  have hf := SixSol20261112.Fuel.Equations.functionChild p tag generalizeCheck generalizeArguments ht
  have values (history : Term ctx) : ∀ i : Fin 4,
      Nonempty (Derivation T (.equal (call (child i) (args index fuel history line))
        ((history ::ᵥ call (child 1) (args index fuel history line) ::ᵥ call (child 2) (args index fuel history line) ::ᵥ call (child 3) (args index fuel history line) ::ᵥ nil).get i))) := by
    intro i
    cases i using Fin.cases with
    | zero =>
      exact SixSol20261112.Fuel.Equations.projection p _ (2 : Fin 4) (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeCheck generalizeArguments ht 0) _
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        exact ⟨.logical (.reflexive _)⟩
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          exact ⟨.logical (.reflexive _)⟩
        | succ i =>
          cases i using Fin.cases with
          | zero =>
            exact ⟨.logical (.reflexive _)⟩
          | succ i =>
            exact Fin.elim0 i
  obtain ⟨oldEq⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag generalizeCheck generalizeArguments ht ot oldValues (values h)
  obtain ⟨newEq⟩ := SixSol20261112.Fuel.Equations.compositionValues p tag generalizeCheck generalizeArguments ht nt newValues (values (HistoryAppend.appendCall atag h tail))
  have hc : Derivation T (.equal (call (tag+1) newValues) (call (tag+1) mixedValues)) := by
    apply Logic.callCongruence T (tag+1) newValues mixedValues
    intro i
    cases i using Fin.cases with
    | zero =>
      exact .logical (.reflexive _)
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        exact Classical.choice (independentEquation contextIndependent arity p (child 1)
          (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeCheck generalizeArguments ht 1)
          ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
      | succ i =>
        cases i using Fin.cases with
        | zero =>
          exact Classical.choice (independentEquation rawIndependent arity p (child 2)
            (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeCheck generalizeArguments ht 2)
            ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
        | succ i =>
          cases i using Fin.cases with
          | zero =>
            exact Classical.choice (independentEquation ref1Independent arity p (child 3)
              (SixSol20261112.Fuel.Equations.argumentChild p tag generalizeCheck generalizeArguments ht 3)
              ctx index fuel (HistoryAppend.appendCall atag h tail) h line)
          | succ i =>
            exact Fin.elim0 i
  obtain ⟨hs⟩ := HistoryRuleSuffix.SuffixProof.internalGeneralizeSuffix arity p (tag+1) atag hf ha ctx h tail
    (call (child 1) ot) (call (child 2) ot) (call (child 3) ot)
  let E := accepts (call tag ot)
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have coreOld := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ oldEq)) he
  have coreNew := Hilbert.Local.mp (.base hs) coreOld
  have out := localTrans _ _ _ (.base newEq) (localTrans _ _ _ (.base hc) coreNew)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge out)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDispatcher.BranchProof
