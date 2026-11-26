module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryAppend.TableEquationsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.InternalProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof List.Vector
open SixSol20261112 NamedArithmeticGraph

theorem wrapperEquation {n ctx : Nat} (p : Program n) (tag : Nat) (x : Program 3)
 (ht : (nodes p)[tag]? = some ⟨3,saturated x⟩) (index fuel line : Term ctx) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (leafCall tag index fuel line) (call (tag+1) (Fuel.inputs index fuel .zero .zero line)))) := by
 let args := index ::ᵥ fuel ::ᵥ line ::ᵥ nil
 have hv : ∀ j : Fin 5, Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call (tag+argumentTag (Fuel.verifier (lifted x)) wrapperArguments j) args)
   ((Fuel.inputs index fuel .zero .zero line).get j))) := by
  intro j
  have hj := Fuel.Equations.argumentChild p tag (Fuel.verifier (lifted x)) wrapperArguments ht j
  cases j using Fin.cases with
  | zero => exact Fuel.Equations.projection p _ (0 : Fin 3) hj args
  | succ j => cases j using Fin.cases with
   | zero => exact Fuel.Equations.projection p _ (1 : Fin 3) hj args
   | succ j => cases j using Fin.cases with
    | zero => exact HistoryAppend.TableEquationsProof.zeroEquation p _ hj args
    | succ j => cases j using Fin.cases with
     | zero => exact HistoryAppend.TableEquationsProof.zeroEquation p _ hj args
     | succ j => cases j using Fin.cases with
      | zero => exact Fuel.Equations.projection p _ (2 : Fin 3) hj args
      | succ j => exact Fin.elim0 j
 exact Fuel.Equations.compositionValues p tag (Fuel.verifier (lifted x)) wrapperArguments ht args
  (Fuel.inputs index fuel .zero .zero line) hv

theorem internalMonotonicity : Targets.InternalMonotonicity := by
 intro n p tag x ht ctx index s t line
 let T := GorbowPRNumeralCalculation.Theory p
 have hv := Fuel.Equations.functionChild p tag (Fuel.verifier (lifted x)) wrapperArguments ht
 obtain ⟨hs⟩ := wrapperEquation p tag x ht index s line
 obtain ⟨ht'⟩ := wrapperEquation p tag x ht index t line
 obtain ⟨hm⟩ := Fuel.InductionProof.openMonotonicity n p (tag+1) (lifted x) hv ctx index s t .zero .zero line
 let H := Fuel.orderGuard s t
 let A := success tag index s line
 let R := success tag index t line
 have hh : Hilbert.Local T ctx [A,H] H := .hypothesis (by simp)
 have ha : Hilbert.Local T ctx [A,H] A := .hypothesis List.mem_cons_self
 have hinner := Hilbert.Local.mp (.base (Fuel.Logic.oneTransport _ _ hs)) ha
 have hnext := Hilbert.Local.mp (.mp (.base hm) hh) hinner
 have hres : Hilbert.Local T ctx [A,H] R :=
  .mp (.base (Fuel.Logic.oneTransport _ _ (Support.equalitySymmetry _ _ ht'))) hnext
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hres))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.InternalProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedAxiomLeaf.InternalProof
