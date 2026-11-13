module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.ReferenceCasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport

def stable {ctx : Nat} (atag ltag : Nat) (index h tail : Term ctx) : Formula ctx :=
  .disj (.equal (HistoryLookup.lookupCall ltag index h) .zero)
    (.equal (HistoryLookup.lookupCall ltag index (HistoryAppend.appendCall atag h tail))
      (HistoryLookup.lookupCall ltag index h))

theorem substStable {m n : Nat} (s : Fin m → Term n) atag ltag (index h tail : Term m) :
    substituteFormula s (stable atag ltag index h tail) =
      stable atag ltag (substitute s index) (substitute s h) (substitute s tail) := by
  simp only [stable,substituteFormula,HistoryAppend.TableLookupProof.substLookup,
    HistoryAppend.PreserveSupportProof.substAppend,substitute]

theorem lookupCases {n ctx : Nat} (p : Program n) atag ltag
    (ha : (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩)
    (hl : (nodes p)[ltag]? = some ⟨2,HistoryLookup.lookup⟩) (index h tail : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p) (stable atag ltag index h tail)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let old := HistoryLookup.lookupCall ltag index h
  let Q := stable atag ltag index h tail
  have hz : Derivation T (.imp (.equal old .zero) Q) := .logical (.orLeft _ _)
  let H := HistoryOrder.SupportProof.predBody old
  obtain ⟨hp⟩ := HistoryAppend.PreserveProof.internalPreserveSome n p atag ltag ha hl (ctx+1)
    (liftTerm index) (liftTerm h) (liftTerm tail) (.var 0)
  have hs : Hilbert.Local T (ctx+1) [H] (.equal (HistoryLookup.lookupCall ltag (liftTerm index) (liftTerm h)) (.succ (.var 0))) := by
    simpa only [H,old,HistoryOrder.SupportProof.predBody,liftTerm,renameTerm,HistoryAppend.TableLookupProof.substLookup] using
      (Hilbert.Local.hypothesis (T := T) (List.mem_cons_self : H ∈ [H]))
  have hn := Hilbert.Local.mp (.base hp) hs
  have he := localTrans _ _ _ hn (HistoryOrder.StepProof.localSym _ _ hs)
  have hq : Hilbert.Local T (ctx+1) [H] (stable atag ltag (liftTerm index) (liftTerm h) (liftTerm tail)) :=
    .mp (.base (.logical (.orRight _ _))) he
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,GorbowPACore.weaken,substStable,liftTerm,renameTerm] using
      Hilbert.Local.finish (Hilbert.Local.discharge hq)
  obtain ⟨he⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨split⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T old
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hz) he) split⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.ReferenceCasesProof
