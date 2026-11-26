module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionIndexValidity.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport
open GorbowSyntax GorbowPRDefiningEquations SixSol20261113 SixSol20261112.Fuel List.Vector
/-- The old substitution context has one extra free slot. A pending old index
task corresponds to a pending new whole term: its marker was suppressed. -/
def taskRelation {ctx : Nat} (l r : Nat) (old new : Term ctx) : Formula ctx :=
 .conj (.equal (call r (old ::ᵥ nil)) (.succ (call r (new ::ᵥ nil))))
  (.disj
   (.conj (.equal (call l (old ::ᵥ nil)) (call l (new ::ᵥ nil)))
    (.disj (.equal (call l (old ::ᵥ nil)) .zero)
     (.equal (call l (old ::ᵥ nil)) (Term.numeral 1))))
   (.conj (.equal (call l (old ::ᵥ nil)) (Term.numeral 2))
    (.equal (call l (new ::ᵥ nil)) .zero)))
/-- Actual aligned SOME lookup entries, with both witness binders explicit. -/
def entryRelation {ctx : Nat} (q l r : Nat) (old new index : Term ctx) : Formula ctx :=
 .all (.imp (.equal (HistoryLookup.lookupCall q (liftTerm index) (liftTerm old)) (.succ (.var 0)))
  (.ex (.conj
   (.equal (HistoryLookup.lookupCall q (liftTerm (liftTerm index)) (liftTerm (liftTerm new))) (.succ (.var 0)))
   (taskRelation l r (.var 1) (.var 0)))))
/-- Arbitrary numeric stacks, equal actual lengths, original lookup/decoder
graphs only. No new map program or native list image is assumed. -/
def stackRelation {ctx : Nat} (len q l r : Nat) (old new : Term ctx) : Formula ctx :=
 .conj (.equal (HistoryLengthOffset.lengthCall len old) (HistoryLengthOffset.lengthCall len new))
  (.all (entryRelation q l r (liftTerm old) (liftTerm new) (.var 0)))
def resultBody {ctx : Nat} (stag len q l r : Nat)
 (newTasks chunk oldResult newResult : Term ctx) : Formula ctx :=
 .conj (.equal (LiteralSyntaxScan.scanCall stag newTasks chunk) (.succ newResult))
  (stackRelation len q l r oldResult newResult)
def results {ctx : Nat} (stag len q l r : Nat)
 (newTasks chunk oldResult : Term ctx) : Formula ctx :=
 .ex (resultBody stag len q l r (liftTerm newTasks) (liftTerm chunk) (liftTerm oldResult) (.var 0))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionChunkTransport
