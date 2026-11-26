module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ImageSuccessorProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SurjectivityProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof

theorem successorWitness {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (code : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (pairSurjective tag code) (pairSurjective tag (.succ code)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := pairSurjective tag (.succ code)
  let H := secondBody tag (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (HistoryKernel.pairCall tag A B) C) :=
    .hypothesis List.mem_cons_self
  have he := localUnary (.succ (.var 0)) _ _ hh
  obtain ⟨hi⟩ := ImageSuccessorProof.imageSuccessor p tag ht A B
  have hout : Hilbert.Local T (ctx+2) [H] (pairSurjective tag (.succ C)) :=
    .mp (.mp (.base (transport tag _ _)) he) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,weakenSurjective,liftTerm,renameTerm,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  exact HBQuantifier.existentialElimination T (firstBody tag code) Q ⟨hinner⟩

/-- Actual PA induction on every source code, with explicit shell successor witnesses. -/
theorem internalPairSurjective : Targets.InternalPairSurjective := by
  intro n p tag ht ctx code
  let T := GorbowPRNumeralCalculation.Theory p
  let phi := pairSurjective tag (.var (0 : Fin (ctx+1)))
  obtain ⟨hz⟩ := zeroWitness (ctx := ctx) p tag ht
  have hb : Derivation T (GorbowStandardInstances.instantiate phi .zero) := by
    simpa only [phi,surjectiveAt] using hz
  obtain ⟨hn⟩ := successorWitness p tag ht (.var (0 : Fin (ctx+1)))
  have hs : Derivation T (.imp phi (GorbowStandardInduction.successorInstance phi)) := by
    simpa only [phi,GorbowStandardInduction.successorInstance,substSurjective,
      substitute,Fin.cases_zero] using hn
  have h := atTerm phi code (HistoryCodec.ArithmeticSupport.induction phi hb hs)
  exact ⟨by simpa only [phi,surjectiveAt] using h⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SurjectivityProof
