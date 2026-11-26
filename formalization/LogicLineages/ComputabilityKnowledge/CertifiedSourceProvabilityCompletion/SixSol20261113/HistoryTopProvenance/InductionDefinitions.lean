module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Induction
open GorbowSyntax
open SixSol20261112.Fuel (liftTerm)
/-- All seven varying arguments are quantified INSIDE the induction formula.
Only the current count is a free term. This is not a supplied invariant. -/
def allFuel {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines context raw tail remaining index : Term ctx) : Formula ctx :=
 .all (provenance itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (liftTerm index) (.var 0))

def allIndex {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines context raw tail remaining : Term ctx) : Formula ctx :=
 .all (allFuel itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (liftTerm remaining) (.var 0))

def allRemaining {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines context raw tail : Term ctx) : Formula ctx :=
 .all (allIndex itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (liftTerm tail) (.var 0))

def allTail {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines context raw : Term ctx) : Formula ctx :=
 .all (allRemaining itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (liftTerm raw) (.var 0))

def allRaw {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines context : Term ctx) : Formula ctx :=
 .all (allTail itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (liftTerm context) (.var 0))

def allContext {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines : Term ctx) : Formula ctx :=
 .all (allRaw itag ptag ctag vtag leftTag rightTag (liftTerm count) (liftTerm lines) (.var 0))

def allLines {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count : Term ctx) : Formula ctx :=
 .all (allContext itag ptag ctag vtag leftTag rightTag (liftTerm count) (.var 0))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance.Induction
