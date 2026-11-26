module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.CodingProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.QuotedVerifierMP.SourceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.PackageProof
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB
open LiteralCheckerAuxiliaries CodingProof

theorem hb2Package (l a : Program 1) (baseX : Program 3) (offset : Nat)
 (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
 (tagG : Nat) (pG : Program 6) (mtag : Nat)
 (hret : LiteralValidatedSource.Retained l a (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG)
 (hmp : LiteralSourceCoreMP.Targets.MPPackage l a (SaturatedAxiomLeaf.saturated baseX) offset pF pR mtag) :
 Targets.HB2Package l a baseX pF pR c := by
 let q := LiteralKernelSource.verifier LiteralSourceCoreMP.valid l a (SaturatedAxiomLeaf.saturated baseX) bound initial finalizer
 let T := S pF pR q
 have hActual : Actual pF pR q c := hret.2.2.2.2.2.2.2.2.1
 intro sigma tau
 let R := rho pF c
 let A := Formula.imp R (Formula.imp sigma tau)
 let B := Formula.imp R sigma
 let C := Formula.imp R tau
 obtain ⟨hdist⟩ := certifiedDistribution pF pR q c hActual sigma tau
 obtain ⟨hmp1⟩ := QuotedVerifierMP.SourceProof.sourceMP l a baseX offset pF pR c tagCK pCK tagG pG mtag hret hmp A (.imp B C)
 obtain ⟨hmp2⟩ := QuotedVerifierMP.SourceProof.sourceMP l a baseX offset pF pR c tagCK pCK tagG pG mtag hret hmp B C
 obtain ⟨heI⟩ := literalPrD pF pR q c hActual (.imp sigma tau)
 obtain ⟨heA⟩ := literalPrD pF pR q c hActual sigma
 obtain ⟨heR⟩ := literalPrD pF pR q c hActual tau
 let G := [prD pF c sigma,prD pF c (.imp sigma tau)]
 have hi : Hilbert.Local T 0 G (prD pF c (.imp sigma tau)) := .hypothesis (by simp [G])
 have ha : Hilbert.Local T 0 G (prD pF c sigma) := .hypothesis List.mem_cons_self
 have hquotedI := Hilbert.Local.mp (.base (.mp (.logical (.andLeft _ _)) heI)) hi
 have hquotedA := Hilbert.Local.mp (.base (.mp (.logical (.andLeft _ _)) heA)) ha
 have hmid := Hilbert.Local.mp (.mp (.base hmp1) (.base hdist)) hquotedI
 have hquotedR := Hilbert.Local.mp (.mp (.base hmp2) hmid) hquotedA
 have hresult := Hilbert.Local.mp (.base (.mp (.logical (.andRight _ _)) heR)) hquotedR
 exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (Hilbert.Local.discharge hresult))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.PackageProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.PublishedSourceHB2.PackageProof
