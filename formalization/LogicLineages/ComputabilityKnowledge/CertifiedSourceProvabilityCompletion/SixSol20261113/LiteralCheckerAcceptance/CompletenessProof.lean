module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.WitnessProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CompletenessProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries WitnessProof
open HistoryCodec.ArithmeticSupport

noncomputable def finalCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    (tag : Nat) (a b requested formula certificate : Term ctx)
    (h : Hilbert.Local T ctx G (.equal a b)) :
    Hilbert.Local T ctx G (.equal (finalCall tag a requested formula certificate) (finalCall tag b requested formula certificate)) := by
  have he := localUnary (finalCall tag (.var 0) (liftTerm requested) (liftTerm formula) (liftTerm certificate)) a b h
  simpa only [finalCall,Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,Support.shiftCancel,Fin.cases_zero] using he

theorem completeBody {n ctx : Nat} (p : Program n) (ftag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (state requested formula certificate raw tail : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (body ptag ctag state requested formula raw tail)
        (.equal (finalCall ftag state requested formula certificate) (.succ .zero)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let B := body ptag ctag state requested formula raw tail
  have hb : Hilbert.Local T ctx [B] B := .hypothesis List.mem_cons_self
  have hformula : Hilbert.Local T ctx [B] (.equal formula (.add raw raw)) := .mp (.base (.logical (.andLeft _ _))) hb
  have hstate : Hilbert.Local T ctx [B] (.equal state (successfulState ptag ctag requested raw tail .zero)) := .mp (.base (.logical (.andRight _ _))) hb
  obtain ⟨he⟩ := ComparisonProof.internalFinishCharacterization n p ftag ptag ctag hf hp hc ctx requested raw tail .zero requested formula certificate
  have hfields : Hilbert.Local T ctx [B] (.conj (.equal requested requested) (.equal formula (.add raw raw))) :=
    .mp (.mp (.base (.logical (.andIntro _ _))) (.base (.logical (.reflexive requested)))) hformula
  have hs := Hilbert.Local.mp (.mp (.base (.logical (.andRight _ _))) (.base he)) hfields
  have hfstate := finalCongruence ftag state _ requested formula certificate hstate
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge (localTrans _ _ _ hfstate hs))⟩

theorem completeWitness {n ctx : Nat} (p : Program n) (ftag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩)
    (state requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (witness ptag ctag state requested formula)
        (.equal (finalCall ftag state requested formula certificate) (.succ .zero)))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := Formula.equal (finalCall ftag state requested formula certificate) (.succ .zero)
  let H := inner ptag ctag (liftTerm state) (liftTerm requested) (liftTerm formula) (.var (0 : Fin (ctx+1)))
  obtain ⟨hb⟩ := completeBody p ftag ptag ctag hf hp hc
    (liftTerm (liftTerm state)) (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula))
    (liftTerm (liftTerm certificate)) (.var (Fin.succ (0 : Fin (ctx+1)))) (.var 0)
  have he : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [H,Q,inner,GorbowPACore.weaken,substituteFormula,finalCall,Logic.substCall,
      List.Vector.map_cons,List.Vector.map_nil,substitute,liftTerm,renameTerm] using hb
  obtain ⟨hi⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨he⟩
  exact HBQuantifier.existentialElimination T (outer ptag ctag state requested formula) Q ⟨hi⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CompletenessProof
