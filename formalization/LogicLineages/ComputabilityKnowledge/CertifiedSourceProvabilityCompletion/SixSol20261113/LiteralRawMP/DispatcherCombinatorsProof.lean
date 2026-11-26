module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherCombinatorsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix HistoryCodec.ArithmeticSupport DispatcherSupportProof

theorem unary {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) arity)
    (f : Program 1) (q : Program arity) (a value : Term ctx)
    (hq : Computes p G q args a) (hf : Computes p G f (a ::ᵥ nil) value) :
    Computes p G (applyOne f q) args value := by
  apply compose p G f (fun _ => q) args (a ::ᵥ nil) value _ hf
  intro i
  cases i using Fin.cases with
  | zero => exact hq
  | succ i => exact Fin.elim0 i

theorem binary {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) arity)
    (f : Program 2) (qa qb : Program arity) (a b value : Term ctx)
    (ha : Computes p G qa args a) (hb : Computes p G qb args b) (hf : Computes p G f (a ::ᵥ b ::ᵥ nil) value) :
    Computes p G (applyTwo f qa qb) args value := by
  apply compose p G f (Fin.cases qa (Fin.cases qb Fin.elim0)) args (a ::ᵥ b ::ᵥ nil) value _ hf
  intro i
  cases i using Fin.cases with
  | zero => exact ha
  | succ i => cases i using Fin.cases with
    | zero => exact hb
    | succ i => exact Fin.elim0 i

theorem chooseZero {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) arity)
    (test yes no : Program arity) (value : Term ctx)
    (htest : Computes p G test args .zero) (hyes : Computes p G yes args value) :
    Computes p G (choose test yes no) args value := by
  intro tag ht
  let g : Fin 3 → Program arity := Fin.cases test (Fin.cases yes (Fin.cases no Fin.elim0))
  obtain ⟨he⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag arity 3 HistoryCodec.select g ht ctx args
  obtain ⟨h0⟩ := htest _ (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 0)
  obtain ⟨h1⟩ := hyes _ (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 1)
  let other := call (tag+argumentTag HistoryCodec.select g 2) args
  have hcg := DispatcherSupportProof.callCongruence (tag+1)
    (List.Vector.ofFn fun i => call (tag+argumentTag HistoryCodec.select g i) args)
    (.zero ::ᵥ value ::ᵥ other ::ᵥ nil) (fun i => by
      cases i using Fin.cases with
      | zero => simpa only [List.Vector.get_ofFn,List.Vector.get_cons_zero] using h0
      | succ i => cases i using Fin.cases with
        | zero => exact h1
        | succ i => cases i using Fin.cases with
          | zero => exact Hilbert.Local.base (.logical (.reflexive other))
          | succ i => exact Fin.elim0 i)
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (tag+1)
    (SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select g ht) value other
  exact ⟨localTrans _ _ _ (.base he) (localTrans _ _ _ hcg (.base hs))⟩

theorem choosePositive {n arity ctx : Nat} (p : Program n) (G : List (Formula ctx)) (args : List.Vector (Term ctx) arity)
    (test yes no : Program arity) (k value : Term ctx)
    (htest : Computes p G test args (.succ k)) (hno : Computes p G no args value) :
    Computes p G (choose test yes no) args value := by
  intro tag ht
  let g : Fin 3 → Program arity := Fin.cases test (Fin.cases yes (Fin.cases no Fin.elim0))
  obtain ⟨he⟩ := GorbowPRSymbolicEquations.Proof.compositionEquation n p tag arity 3 HistoryCodec.select g ht ctx args
  obtain ⟨h0⟩ := htest _ (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 0)
  obtain ⟨h2⟩ := hno _ (SixSol20261112.Fuel.Equations.argumentChild p tag HistoryCodec.select g ht 2)
  let other := call (tag+argumentTag HistoryCodec.select g 1) args
  have hcg := DispatcherSupportProof.callCongruence (tag+1)
    (List.Vector.ofFn fun i => call (tag+argumentTag HistoryCodec.select g i) args)
    (.succ k ::ᵥ other ::ᵥ value ::ᵥ nil) (fun i => by
      cases i using Fin.cases with
      | zero => exact h0
      | succ i => cases i using Fin.cases with
        | zero => exact Hilbert.Local.base (.logical (.reflexive other))
        | succ i => cases i using Fin.cases with
          | zero => exact h2
          | succ i => exact Fin.elim0 i)
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectPositive p (tag+1)
    (SixSol20261112.Fuel.Equations.functionChild p tag HistoryCodec.select g ht) other value k
  exact ⟨localTrans _ _ _ (.base he) (localTrans _ _ _ hcg (.base hs))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherCombinatorsProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralRawMP.DispatcherCombinatorsProof
