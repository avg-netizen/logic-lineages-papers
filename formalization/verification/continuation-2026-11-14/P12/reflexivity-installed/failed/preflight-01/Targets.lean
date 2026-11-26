module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Every member of the structural carrier has an actual registry lookup,
not merely an extensionally equal evaluator. -/
def BundleInstallation : Prop := ∀ (xs : List Packed) n (p : Program n) tag,
 (nodes p)[tag]? = some ⟨6,bundle xs⟩ →
 ∀ a ∈ xs, ∃ atag, (nodes p)[atag]? = some a
/-- Fix the term template BEFORE selecting the source. Retain the ENTIRE CK,
producer, validator, MP, fuel, saturated-axiom, closure and HB2 packages at
identical witnesses, and derive saturated reflexivity acceptance in that SAME
source for all symbolic runtime values/index/fuel. No installation, acceptance,
source equality, coherent quotation or HB3 premise is added. -/
def SameSourceCertificate : Prop := ∀ k (t : Term k),
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 ∃ I : TwoSol20261113.ReflexivityCertificate.Installation
   (root pF pR old a baseX) t old a (SaturatedAxiomLeaf.saturated baseX),
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (ReflexivitySource.logical old) a
  (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 ReflexivityPackages.Packages old a baseX offset pF pR c mtag xtag ∧
 ∀ ctx (values : List.Vector (Term ctx) k) (index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier old a baseX))
  (SixSol20261112.Fuel.success (GorbowNamedInternalProvability.checkerTag pF)
   index fuel .zero
   (.add (TwoSol20261113.ReflexivityCertificate.raw I.etag values)
    (TwoSol20261113.ReflexivityCertificate.raw I.etag values))
   (TwoSol20261113.ReflexivityCertificate.certificate I.ctag I.qtag values)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.ReflexivityInstalled.Targets
