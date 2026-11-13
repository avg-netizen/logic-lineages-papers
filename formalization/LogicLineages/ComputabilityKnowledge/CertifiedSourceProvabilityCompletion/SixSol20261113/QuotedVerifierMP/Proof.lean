module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.CodeTransportProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP.StatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Proof
open GorbowSyntax GorbowTheoryProof
open SixSol20261112.Fuel NamedArithmeticGraph CodeTransportProof QuotationProof

theorem internalQuotedMP : Targets.InternalQuotedMP := by
 intro l a baseX n p itag ltag atag ptag ctag dtag droptag rtag dispatcherTag hi hl ha hp hc hd hdrop hr hdispatch
   mtag qtag vtag hm hq hv ctx index sigma tau
 let T := GorbowPRNumeralCalculation.Theory p
 let rawS : Term ctx := Term.numeral (GorbowCodeConstructors.formulaNumber sigma)
 let rawT : Term ctx := Term.numeral (GorbowCodeConstructors.formulaNumber tau)
 obtain ⟨hraw⟩ := ExistentialVerifierMP.StatementChecks.internalProvabilityMP l a baseX n p
  itag ltag atag ptag ctag dtag droptag rtag dispatcherTag hi hl ha hp hc hd hdrop hr hdispatch
  mtag qtag vtag hm hq hv ctx index .zero rawS rawT
 obtain ⟨himp⟩ := doubleImplicationQuote (ctx := ctx) p atag ctag ha hc sigma tau
 obtain ⟨hs⟩ := doubleQuote T ctx sigma
 obtain ⟨ht⟩ := doubleQuote T ctx tau
 let I := ExistentialVerifierMP.provability vtag index .zero (Term.numeral (GorbowSortedSyntaxCode.formulaCode (.imp sigma tau)))
 let A := ExistentialVerifierMP.provability vtag index .zero (Term.numeral (GorbowSortedSyntaxCode.formulaCode sigma))
 have hI : Hilbert.Local T ctx [A,I] I := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
 have hA : Hilbert.Local T ctx [A,I] A := .hypothesis List.mem_cons_self
 have hi' := Hilbert.Local.mp (.base (codeTransport vtag index .zero _ _ (Support.equalitySymmetry _ _ himp))) hI
 have ha' := Hilbert.Local.mp (.base (codeTransport vtag index .zero _ _ (Support.equalitySymmetry _ _ hs))) hA
 have hout := Hilbert.Local.mp (.base (codeTransport vtag index .zero _ _ ht)) (.mp (.mp (.base hraw) hi') ha')
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hout))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.Proof
