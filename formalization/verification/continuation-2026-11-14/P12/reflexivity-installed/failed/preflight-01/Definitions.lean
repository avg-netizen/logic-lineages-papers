module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityPackages.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityFuel.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB SixSol20261113
/-- Finite structural carrier of heterogeneous ASTs. No evaluation claim about
this carrier is required; the genuine semantic producer remains separately installed. -/
def bundle : List Packed → Program 6
 | [] => .projection 0
 | a :: rest => InstalledProducerExtra.container
   (InstalledProducerExtra.extraWrapper a.2) (bundle rest)
/-- Every AST required by the existing exact certificate interface, plus the
original MP constructor, fixed before the source registry is selected. -/
def items {k : Nat} (t : Term k) (old a : Program 1) (x : Program 3) : List Packed :=
 [⟨4,LiteralRawMP.constructor⟩,
  ⟨k,LiteralReflexivityQuote.lineQuote t⟩,
  ⟨k,LiteralEqualityQuote.equalityQuote t t⟩,
  ⟨k,LiteralTemplateQuote.templateQuote t⟩,
  ⟨2,HistoryCodec.pair⟩,⟨2,HistoryCodec.cons⟩,⟨2,HistoryAppend.append⟩,
  ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩,
  ⟨2,LiteralSyntaxValidator.formulaValidator⟩,
  ⟨1,TwoSol20261113.ReflexivityCertificate.validity⟩,
  ⟨1,TwoSol20261113.ReflexivityCertificate.logical old⟩,
  ⟨4,TwoSol20261113.ReflexivityCertificate.dispatcher old a x⟩,
  ⟨4,SixSol20261112.HistoryMachine.iterator (TwoSol20261113.ReflexivityCertificate.kernel old a x)⟩,
  ⟨5,TwoSol20261113.ReflexivityCertificate.checker old a x⟩]
abbrev verifier (old a : Program 1) (baseX : Program 3) : Program 5 :=
 ReflexivityFuel.checker old a (SaturatedAxiomLeaf.saturated baseX)
abbrev root (pF pR old a : Program 1) (baseX : Program 3) : Program 4 :=
 GorbowSourceRegistryPadding.root (augmented pF (verifier old a baseX)) pR
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled
