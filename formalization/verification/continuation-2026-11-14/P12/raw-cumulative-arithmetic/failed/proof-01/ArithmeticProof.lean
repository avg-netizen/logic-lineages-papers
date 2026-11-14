module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.ArithmeticProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

/-- Actual symbolic selector-range proof: equal branches make the output
independent of the recognizer. No native evaluation is reflected internally. -/
theorem chooseBoth {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx))
 (test yes no : Program arity) (args : List.Vector (Term ctx) arity) (value : Term ctx)
 (hy : Computes p G yes args value) (hn : Computes p G no args value) :
 Computes p G (choose test yes no) args value := by
 intro tag ht
 let g : Fin 3 → Program arity := Fin.cases test (Fin.cases yes (Fin.cases no Fin.elim0))
 obtain ⟨he⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag arity 3 HistoryCodec.select g ht ctx args
 obtain ⟨h1⟩ := hy _ (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 1)
 obtain ⟨h2⟩ := hn _ (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 2)
 let tested := call (tag+argumentTag HistoryCodec.select g 0) args
 have hcg := callCongruence (tag+1)
  (List.Vector.ofFn fun i => call (tag+argumentTag HistoryCodec.select g i) args)
  (tested ::ᵥ value ::ᵥ value ::ᵥ nil) (fun i => by
   cases i using Fin.cases with
   | zero => exact .base (.logical (.reflexive tested))
   | succ i => cases i using Fin.cases with
     | zero => exact h1
     | succ i => cases i using Fin.cases with
       | zero => exact h2
       | succ i => exact Fin.elim0 i)
 obtain ⟨hr⟩ := HistoryKernel.RangeProof.selectRange p (tag+1)
  (SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select g ht) tested value value
 let E := Formula.equal (call (tag+1) (tested ::ᵥ value ::ᵥ value ::ᵥ nil)) value
 have hout : Derivation (GorbowPRNumeralCalculation.Theory p) E :=
  .mp (.mp (.mp (.logical (.orElim E E E)) (Hilbert.identity E)) (Hilbert.identity E)) hr
 exact ⟨localTrans _ _ _ (.base he) (localTrans _ _ _ hcg (.base hout))⟩

theorem internalAddZero : Targets.InternalAddZero := by
 intro n p old qtag ltag ptag ctag atag vtag hq hl hp hc ha hv ctx raw
 let T := GorbowPRNumeralCalculation.Theory p
 let H := RawReflexivityDispatcher.valid vtag raw
 let G := [H]
 let line := RawAddZero.lineCall qtag raw
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hinner : Computes p G (RawAddZero.arithmeticLeaf old) (line ::ᵥ nil) (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := RawAddZero.StatementChecks.exactInternalArithmetic n p old qtag tag ptag ctag atag vtag
   hq ht hp hc ha hv ctx raw
  exact ⟨.mp (.base h) hh⟩
 have hone := constantValue p G (line ::ᵥ nil) 1
 obtain ⟨hout⟩ := chooseBoth p G RawAddSucc.recognizer (RawAddZero.arithmeticLeaf old)
  (constant 1 1) (line ::ᵥ nil) (.succ .zero) hinner hone ltag hl
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.ArithmeticProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.ArithmeticProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.ArithmeticProof.chooseBoth
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawCumulativeArithmetic.ArithmeticProof.internalAddZero
