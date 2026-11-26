module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRunSplice.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance
open GorbowSyntax GorbowPRProgram GorbowPRChildTags GorbowPRDefiningEquations List.Vector
open SixSol20261112.HistoryMachine HistoryRuleSuffix

/-- Actual kernel occurrence inside the unchanged literal iterator. -/
def kernelTag (itag : Nat) : Nat := itag + stepTag iterationBase + 1
/-- Exact select arguments of lineDispatcher, whose first argument is validity.
The select tests nonzero, not equality to one. -/
def dispatcherArguments (v l a : Program 1) (x : Program 3) : Fin 3 → Program 4 :=
 Fin.cases (applyOne v HistoryDispatcher.lineCode)
   (Fin.cases (constant 4 0) (Fin.cases (HistoryDispatcher.ruleDispatcher l a x) Fin.elim0))
/-- Actual function child v of the validity wrapper, not an unrelated installed copy. -/
def validityTag (itag : Nat) (v l a : Program 1) (x : Program 3) : Nat :=
 HistoryKernel.TransitionEquationsProof.dispatcherTag (kernelTag itag) v l a x +
   argumentTag HistoryCodec.select (dispatcherArguments v l a x) 0 + 1

def lineFields {ctx : Nat} (vtag leftTag rightTag : Nat)
    (line context raw : Term ctx) : Formula ctx :=
 .conj (.equal (call leftTag (line ::ᵥ nil)) context)
   (.conj (.equal (call leftTag (call rightTag (line ::ᵥ nil) ::ᵥ nil)) raw)
     (.neg (.equal (call vtag (line ::ᵥ nil)) .zero)))
/-- One genuine internal existential: the consumed line itself. Rule and payload
remain untouched and unrestricted. No assertion that arbitrary v is Boolean. -/
def topWitness {ctx : Nat} (vtag leftTag rightTag : Nat)
    (context raw : Term ctx) : Formula ctx :=
 .ex (lineFields vtag leftTag rightTag (.var 0)
   (SixSol20261112.Fuel.liftTerm context) (SixSol20261112.Fuel.liftTerm raw))

/-- Arbitrary count, arbitrary remaining lines. Empty initial history prevents
an unvalidated preexisting top; successful final stutters must be handled. -/
def provenance {ctx : Nat} (itag ptag ctag vtag leftTag rightTag : Nat)
    (count lines context raw tail remaining index fuel : Term ctx) : Formula ctx :=
 .imp (.equal (HistoryRunSplice.run itag ptag count (.succ .zero) lines index fuel)
   (HistoryRunSplice.state ptag
     (.succ (HistoryLookup.consCall ctag (HistoryKernel.pairCall ptag context raw) tail)) remaining))
   (topWitness vtag leftTag rightTag context raw)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryTopProvenance
