module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplicationSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Actual candidate is the original repeated-tail suffix of the raw stream.
The test's second argument is the unchanged surrounding original line code. -/
def candidate : Program 4 := applyTwo HistoryLookup.drop (.projection 0) (.projection 2)
def testAt (test : Program 2) : Program 4 := applyTwo test candidate (.projection 3)
def positive (test : Program 2) : Program 4 := choose (testAt test) (constant 4 0) (constant 4 1)
/-- Actual Boolean latch: preserve success, otherwise evaluate current suffix.
Inputs [position,previousFlag,originalRaw,originalLine]. -/
def step (test : Program 2) : Program 4 := choose (.projection 1) (positive test) (constant 4 1)
/-- Inputs [count,raw,line]. Exactly count original suffixes are tested, including
position zero when count is positive. No unbounded search or parser oracle. -/
def search (test : Program 2) : Program 3 := .recursion (constant 2 0) (step test)
def searchCall {ctx : Nat} (tag : Nat) (count raw line : Term ctx) : Term ctx :=
 call tag (count ::ᵥ raw ::ᵥ line ::ᵥ nil)
def testCall {ctx : Nat} (tag : Nat) (suffix line : Term ctx) : Term ctx := call tag (suffix ::ᵥ line ::ᵥ nil)
structure Installation {n : Nat} (p : Program n) (test : Program 2) where
 testTag : Nat
 dropTag : Nat
 searchTag : Nat
 ht : (nodes p)[testTag]? = some ⟨2,test⟩
 hd : (nodes p)[dropTag]? = some ⟨2,HistoryLookup.drop⟩
 hs : (nodes p)[searchTag]? = some ⟨3,search test⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixSearch
