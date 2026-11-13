module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.PreservationProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.AxiomProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryDispatcher SaturatedDispatcherFuel.IndependenceProof SaturatedDispatcherFuel.PreservationProof

theorem axiomEquation {n ctx : Nat} (p : Program n) (tag : Nat) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨4,.composition (SaturatedAxiomLeaf.saturated x) axiomArguments⟩)
 (index fuel h line : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (args index fuel h line)) (SaturatedAxiomLeaf.leafCall (tag+1) index fuel line))) := by
 let values := index ::ᵥ fuel ::ᵥ line ::ᵥ nil
 have hv : ∀ j : Fin 3, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call (tag+argumentTag (SaturatedAxiomLeaf.saturated x) axiomArguments j) (args index fuel h line)) (values.get j))) := by
  intro j
  have hj := Equations.argumentChild p tag (SaturatedAxiomLeaf.saturated x) axiomArguments ht j
  cases j using Fin.cases with
  | zero => exact Equations.projection p _ (0 : Fin 4) hj (args index fuel h line)
  | succ j => cases j using Fin.cases with
   | zero => exact Equations.projection p _ (1 : Fin 4) hj (args index fuel h line)
   | succ j => cases j using Fin.cases with
    | zero => exact Equations.projection p _ (3 : Fin 4) hj (args index fuel h line)
    | succ j => exact Fin.elim0 j
 exact Equations.compositionValues p tag (SaturatedAxiomLeaf.saturated x) axiomArguments ht
  (args index fuel h line) values hv

theorem axiomPreserves (x : Program 3) : Preserves (.composition (SaturatedAxiomLeaf.saturated x) axiomArguments) := by
 intro n p tag ht ctx index s t h line
 let T := GorbowPRNumeralCalculation.Theory p
 have hx := Equations.functionChild p tag (SaturatedAxiomLeaf.saturated x) axiomArguments ht
 obtain ⟨hm⟩ := SaturatedAxiomLeaf.InternalProof.internalMonotonicity n p (tag+1) x hx ctx index s t line
 obtain ⟨hs⟩ := axiomEquation p tag x ht index s h line
 obtain ⟨ht'⟩ := axiomEquation p tag x ht index t h line
 let H := orderGuard s t
 let A := HistoryDispatcher.SelectProof.accepts (call tag (args index s h line))
 have hh : Hilbert.Local T ctx [A,H] H := .hypothesis (by simp)
 have ha : Hilbert.Local T ctx [A,H] A := .hypothesis List.mem_cons_self
 have hinner := Hilbert.Local.mp (.base (Logic.oneTransport _ _ hs)) ha
 have hnext := Hilbert.Local.mp (.mp (.base hm) hh) hinner
 have hres := Hilbert.Local.mp (.base (Logic.oneTransport _ _ (Support.equalitySymmetry _ _ ht'))) hnext
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hres))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.AxiomProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.AxiomProof
