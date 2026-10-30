module

public import LogicLineages.ComputabilityKnowledge.GorbowProofChecker

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowProofChecker
open GorbowSyntax GorbowPACore
open LogicLineages.ComputabilityKnowledge.GorbowProofChecker

def ReferenceBounds : Prop := ∀ history line, lineCheck history line = true →
  (rule line = 2 → (payload line).2.2.1 < history.length ∧ (payload line).2.2.2 < history.length) ∧
  (rule line = 3 → (payload line).2.2.1 < history.length)

def RunConcatenation : Prop := ∀ history a b,
  run history (a++b) = (run history a).bind (fun next => run next b)

def HistorySoundness : Prop := ∀ history, SoundHistory history → ∀ lines next,
  run history lines = some next → SoundHistory next

def CompilationShape : Prop := ∀ (n : Nat) (φ : Formula n) (p : Proof φ),
  0 < (proofLines p).length ∧ (lineConclusions (proofLines p)).head? = some (n,GorbowFormulaPrefixCode.encode φ)

def CompilationCorrectness : Prop := ∀ (n : Nat) (φ : Formula n) (p : Proof φ) (history : History),
  run history (proofLines p) = some (lineConclusions (proofLines p) ++ history)

def CertificateEquivalence : Prop := ∀ n raw,
  (∃ lines, verifies n raw lines = true) ↔
  ∃ φ : Formula n, raw = GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Proof φ)

def UniformPrograms : Prop :=
  Primrec (fun p : History × Line => ruleCheck p.1 p.2) ∧
  Primrec (fun p : History × Line => lineCheck p.1 p.2) ∧
  Primrec (fun p : Option History × Line => step p.1 p.2) ∧
  Primrec (fun p : History × List Line => run p.1 p.2) ∧
  Primrec checkProof ∧
  Primrec (fun p : Nat × List Nat × List Line => verifies p.1 p.2.1 p.2.2)

def Target : Prop := ReferenceBounds ∧ RunConcatenation ∧ HistorySoundness ∧ CompilationShape ∧
  CompilationCorrectness ∧ CertificateEquivalence ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowProofChecker
