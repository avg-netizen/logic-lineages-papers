module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.RecurrenceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261113 SixSol20261113.HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open LiteralRawMP.DispatcherSupportProof LiteralRawMP.DispatcherCombinatorsProof LiteralRawMP.DispatcherPrimitivesProof

theorem next {n ctx : Nat} (p : Program n) (test : Program 2) (I : Installation p test)
 (G : List (Formula ctx)) (count raw line : Term ctx)
 (hstep : Computes p G (step test)
  (count ::ᵥ searchCall I.searchTag count raw line ::ᵥ raw ::ᵥ line ::ᵥ nil) (.succ .zero)) :
 Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory p) ctx G
  (.equal (searchCall I.searchTag (.succ count) raw line) (.succ .zero))) := by
 have hs := SixSol20261112.Fuel.Equations.recursionStepChild p I.searchTag (constant 2 0) (step test) I.hs
 obtain ⟨hr⟩ := GorbowPRSymbolicEquations.Proof.recursionSuccessorEquation n p I.searchTag 2 (constant 2 0) (step test) I.hs ctx count (raw ::ᵥ line ::ᵥ nil)
 obtain ⟨he⟩ := hstep _ hs
 exact ⟨localTrans _ _ _ (.base hr) he⟩

theorem internalPersistence : Targets.InternalPersistence := by
 intro n p test I ctx count raw line
 let T := GorbowPRNumeralCalculation.Theory p
 let H := Formula.equal (searchCall I.searchTag count raw line) (.succ .zero)
 let G := [H]
 let args := count ::ᵥ searchCall I.searchTag count raw line ::ᵥ raw ::ᵥ line ::ᵥ nil
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hp : Computes p G (.projection (1 : Fin 4)) args (.succ .zero) := by
  intro tag ht
  obtain ⟨h⟩ := projection p G args 1 tag ht
  exact ⟨localTrans _ _ _ h hh⟩
 have hs := choosePositive p G args (.projection 1) (positive test) (constant 4 1) .zero (.succ .zero)
  hp (constantValue p G args 1)
 obtain ⟨h⟩ := next p test I G count raw line hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

theorem witnessNext {n ctx : Nat} (p : Program n) (test : Program 2) (I : Installation p test)
 (i raw line : Term ctx) : Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (.equal (testCall I.testTag (HistoryLookup.DropEquationsProof.dropCall I.dropTag i raw) line) (.succ .zero))
  (.equal (searchCall I.searchTag (.succ i) raw line) (.succ .zero)))) := by
 let T := GorbowPRNumeralCalculation.Theory p
 let d := HistoryLookup.DropEquationsProof.dropCall I.dropTag i raw
 let H := Formula.equal (testCall I.testTag d line) (.succ .zero)
 let G := [H]
 let args := i ::ᵥ searchCall I.searchTag i raw line ::ᵥ raw ::ᵥ line ::ᵥ nil
 have hh : Hilbert.Local T ctx G H := .hypothesis List.mem_cons_self
 have hd : Computes p G candidate args d := binary p G args HistoryLookup.drop (.projection 0) (.projection 2) i raw d
  (projection p G args 0) (projection p G args 2) (copies p G HistoryLookup.drop I.dropTag I.hd (i ::ᵥ raw ::ᵥ nil))
 have ht : Computes p G test (d ::ᵥ line ::ᵥ nil) (.succ .zero) := by
  intro tag htag
  obtain ⟨h⟩ := copies p G test I.testTag I.ht (d ::ᵥ line ::ᵥ nil) tag htag
  exact ⟨localTrans _ _ _ h hh⟩
 have htest : Computes p G (testAt test) args (.succ .zero) :=
  binary p G args test candidate (.projection 3) d line (.succ .zero) hd (projection p G args 3) ht
 have hpos : Computes p G (positive test) args (.succ .zero) :=
  choosePositive p G args (testAt test) (constant 4 0) (constant 4 1) .zero (.succ .zero) htest (constantValue p G args 1)
 have hs : Computes p G (step test) args (.succ .zero) :=
  RawCumulativeArithmetic.ArithmeticProof.chooseBoth p G (.projection 1) (positive test) (constant 4 1) args (.succ .zero) hpos (constantValue p G args 1)
 obtain ⟨h⟩ := next p test I G i raw line hs
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge h)⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.RecurrenceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.RecurrenceProof
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.RecurrenceProof.internalPersistence
#print axioms LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch.RecurrenceProof.witnessNext
