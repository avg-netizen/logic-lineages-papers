module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddRightCongruence.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Literal candidate is the current natural index, not a parsed or guessed term.
The test receives [candidate, unchanged originalLine]. -/
def testAt (test : Program 2) : Program 3 := applyTwo test (.projection 0) (.projection 2)
def positive (test : Program 2) : Program 3 := choose (testAt test) (constant 3 0) (constant 3 1)
def step (test : Program 2) : Program 3 := choose (.projection 1) (positive test) (constant 3 1)
/-- Inputs [count,line]. Exactly candidates 0,...,count-1; actual PR Boolean latch. -/
def search (test : Program 2) : Program 2 := .recursion (constant 1 0) (step test)
def searchCall {ctx : Nat} (tag : Nat) (count line : Term ctx) : Term ctx := call tag (count ::ᵥ line ::ᵥ nil)
def testCall {ctx : Nat} (tag : Nat) (candidate line : Term ctx) : Term ctx := call tag (candidate ::ᵥ line ::ᵥ nil)
structure Installation {n : Nat} (p : Program n) (test : Program 2) where
 testTag : Nat
 searchTag : Nat
 ht : (nodes p)[testTag]? = some ⟨2,test⟩
 hs : (nodes p)[searchTag]? = some ⟨2,search test⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumericSearch
