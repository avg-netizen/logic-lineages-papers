module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.RecurrenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem next {n ctx : Nat} (p : Program n) (test : Program 2) (I : Installation p test)
 (G : List (Formula ctx)) (count line : Term ctx)
 (hstep : Computes p G (step test)
  (count ::ᵥ searchCall I.searchTag count line ::ᵥ line ::ᵥ nil) (.succ .zero)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (searchCall I.searchTag (.succ count) line) (.succ .zero))) := by
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p I.searchTag (constant 1 0) (step test) I.hs
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.searchTag 1 (constant 1 0) (step test) I.hs ctx count (line ::ᵥ nil)
 obtain ⟨he⟩ := hstep _ hs
 exact ⟨localTrans _ _ _ (.base hr) he⟩

theorem internalPersistence : Targets.InternalPersistence := by
 intro n p test I ctx count line
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (searchCall I.searchTag count line) (.succ .zero)
 let G := [H]
 let args := count ::ᵥ searchCall I.searchTag count line ::ᵥ line ::ᵥ nil
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hp : Computes p G (.projection (1 : Fin 3)) args (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := projection p G args 1 tag ht
  exact ⟨localTrans _ _ _ h hh⟩
 have hs := choosePositive p G args (.projection 1) (positive test) (constant 3 1) .zero (.succ .zero)
  hp (constantValue p G args 1)
 obtain ⟨h⟩ := next p test I G count line hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

theorem witnessNext {n ctx : Nat} (p : Program n) (test : Program 2) (I : Installation p test)
 (i line : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (testCall I.testTag i line) (.succ .zero))
  (.equal (searchCall I.searchTag (.succ i) line) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (testCall I.testTag i line) (.succ .zero)
 let G := [H]
 let args := i ::ᵥ searchCall I.searchTag i line ::ᵥ line ::ᵥ nil
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have ht : Computes p G test (i ::ᵥ line ::ᵥ nil) (.succ .zero) := by
  intro tag htag
  obtain ⟨h⟩ := copies p G test I.testTag I.ht (i ::ᵥ line ::ᵥ nil) tag htag
  exact ⟨localTrans _ _ _ h hh⟩
 have htest : Computes p G (testAt test) args (.succ .zero) :=
  binary p G args test (.projection 0) (.projection 2) i line (.succ .zero) (projection p G args 0) (projection p G args 2) ht
 have hpos : Computes p G (positive test) args (.succ .zero) :=
  choosePositive p G args (testAt test) (constant 3 0) (constant 3 1) .zero (.succ .zero) htest (constantValue p G args 1)
 have hs : Computes p G (step test) args (.succ .zero) :=
  RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G (.projection 1) (positive test) (constant 3 1) args (.succ .zero) hpos (constantValue p G args 1)
 obtain ⟨h⟩ := next p test I G i line hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.RecurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.RecurrenceProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.RecurrenceProof.internalPersistence
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch.RecurrenceProof.witnessNext
