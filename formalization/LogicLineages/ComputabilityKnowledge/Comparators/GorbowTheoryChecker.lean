module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryChecker
open GorbowSyntax GorbowTheoryProof GorbowProofChecker
open LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker

def AxiomExact : Prop := ∀ axCheck n raw p,
  GorbowTheoryChecker.axiomCheck axCheck n raw p=true ↔ ∃ σ : Sentence,
    p=(0,[GorbowFormulaPrefixCode.encode σ],0,0) ∧ ProgramTheory axCheck σ ∧
    raw=GorbowFormulaPrefixCode.encode (weakenClosed n σ)

def RuleDispatch : Prop := ∀ axCheck history line,
  (rule line≠4 → GorbowTheoryChecker.ruleCheck axCheck history line=GorbowProofChecker.ruleCheck history line) ∧
  (rule line=4 → GorbowTheoryChecker.ruleCheck axCheck history line=axiomCheck axCheck (context line) (conclusion line) (payload line)) ∧
  (4<rule line → GorbowTheoryChecker.ruleCheck axCheck history line=false)

def ReferenceBounds : Prop := ∀ axCheck history line, GorbowTheoryChecker.lineCheck axCheck history line=true →
  (rule line=2 → (payload line).2.2.1<history.length ∧ (payload line).2.2.2<history.length) ∧
  (rule line=3 → (payload line).2.2.1<history.length)

def RunConcatenation : Prop := ∀ axCheck history a b,
  GorbowTheoryChecker.run axCheck history (a++b)=
    (GorbowTheoryChecker.run axCheck history a).bind (fun next => GorbowTheoryChecker.run axCheck next b)

def HistorySoundness : Prop := ∀ axCheck history, GorbowTheoryChecker.SoundHistory axCheck history → ∀ lines next,
  GorbowTheoryChecker.run axCheck history lines=some next → GorbowTheoryChecker.SoundHistory axCheck next

def CompilationShape : Prop := ∀ axCheck n (φ : Formula n) (p : Derivation (ProgramTheory axCheck) φ),
  0<(GorbowTheoryChecker.proofLines axCheck p).length ∧
  (lineConclusions (GorbowTheoryChecker.proofLines axCheck p)).head?=some (n,GorbowFormulaPrefixCode.encode φ)

def CompilationCorrectness : Prop := ∀ axCheck n (φ : Formula n) (p : Derivation (ProgramTheory axCheck) φ) history,
  GorbowTheoryChecker.run axCheck history (GorbowTheoryChecker.proofLines axCheck p)=
    some (lineConclusions (GorbowTheoryChecker.proofLines axCheck p)++history)

def CertificateEquivalence : Prop := ∀ axCheck n raw,
  (∃ lines, GorbowTheoryChecker.verifies axCheck n raw lines=true) ↔
  ∃ φ : Formula n, raw=GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Derivation (ProgramTheory axCheck) φ)

def MalformedRejection : Prop := ∀ axCheck n raw,
  GorbowSyntaxValidation.validFormula n raw=false → ∀ lines, GorbowTheoryChecker.verifies axCheck n raw lines=false

def UniformPrograms : Prop := ∀ axCheck, Primrec axCheck →
  Primrec (fun p : Nat × List Nat × Payload => axiomCheck axCheck p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : History × Line => GorbowTheoryChecker.ruleCheck axCheck p.1 p.2) ∧
  Primrec (fun p : History × Line => GorbowTheoryChecker.lineCheck axCheck p.1 p.2) ∧
  Primrec (fun p : Option History × Line => GorbowTheoryChecker.step axCheck p.1 p.2) ∧
  Primrec (fun p : History × List Line => GorbowTheoryChecker.run axCheck p.1 p.2) ∧
  Primrec (GorbowTheoryChecker.checkProof axCheck) ∧
  Primrec (fun p : Nat × List Nat × List Line => GorbowTheoryChecker.verifies axCheck p.1 p.2.1 p.2.2)

def Target : Prop := AxiomExact ∧ RuleDispatch ∧ ReferenceBounds ∧ RunConcatenation ∧ HistorySoundness ∧
  CompilationShape ∧ CompilationCorrectness ∧ CertificateEquivalence ∧ MalformedRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTheoryChecker
