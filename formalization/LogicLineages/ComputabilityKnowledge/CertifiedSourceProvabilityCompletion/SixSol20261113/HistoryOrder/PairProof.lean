module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.SplitProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.PairProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport SupportProof StepProof

theorem substLowerValue {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substituteFormula sub (lowerValue tag a b) = lowerValue tag (substitute sub a) (substitute sub b) := by
  simp only [lowerValue,HistoryDifference.pairCall,substituteFormula,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem substUpperValue {m n : Nat} (sub : Fin m → Term n) tag (a b : Term m) :
    substituteFormula sub (upperValue tag a b) = upperValue tag (substitute sub a) (substitute sub b) := by
  simp only [upperValue,HistoryDifference.pairCall,substituteFormula,Logic.substCall,
    List.Vector.map_cons,List.Vector.map_nil,substitute]

theorem lowerValueAt {ctx : Nat} tag (a b : Term ctx) :
    GorbowStandardInstances.instantiate (lowerValue tag (liftTerm a) (.var 0)) b = lowerValue tag a b := by
  simp only [GorbowStandardInstances.instantiate,substLowerValue,substitute,
    liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem upperValueAt {ctx : Nat} tag (a b : Term ctx) :
    GorbowStandardInstances.instantiate (upperValue tag (.var 0) (liftTerm b)) a = upperValue tag a b := by
  simp only [GorbowStandardInstances.instantiate,substUpperValue,substitute,
    liftTerm,Support.shiftCancel,Fin.cases_zero]

theorem weakenLowerValue {ctx : Nat} tag (a b : Term ctx) :
    GorbowPACore.weaken (lowerValue tag a b) = lowerValue tag (liftTerm a) (liftTerm b) := by
  rw [GorbowPACore.weaken,substLowerValue]
  rfl

theorem weakenUpperValue {ctx : Nat} tag (a b : Term ctx) :
    GorbowPACore.weaken (upperValue tag a b) = upperValue tag (liftTerm a) (liftTerm b) := by
  rw [GorbowPACore.weaken,substUpperValue]
  rfl

theorem pairLowerOrder : Targets.PairLowerOrder := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let A := liftTerm a
  let B := liftTerm b
  let E := Term.add A (.succ (.var 0))
  let H := lowerBody a b
  obtain ⟨hsector⟩ := HistoryDifference.PairProof.pairLowerSector n p tag ht (ctx+1) A (.var 0)
  have hh : Hilbert.Local T (ctx+1) [H] (.equal B E) := .hypothesis List.mem_cons_self
  have hr : Derivation T (.imp (.equal E B) (.imp (lowerValue tag A E) (lowerValue tag A B))) := by
    have d := Derivation.logical (A := T)
      (.equalityReplace (lowerValue tag (liftTerm A) (.var 0)) E B)
    rwa [GorbowPACore.logicalFormula,lowerValueAt,lowerValueAt] at d
  have hout : Hilbert.Local T (ctx+1) [H] (lowerValue tag A B) :=
    .mp (.mp (.base hr) (localSym B E hh)) (.base hsector)
  have hbody : Derivation T (.imp (lowerBody a b) (GorbowPACore.weaken (lowerValue tag a b))) := by
    rw [weakenLowerValue]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T (lowerBody a b) (lowerValue tag a b) ⟨hbody⟩

theorem pairUpperOrder : Targets.PairUpperOrder := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  let A := liftTerm a
  let B := liftTerm b
  let E := Term.add B (.var 0)
  let H := upperBody a b
  obtain ⟨hsector⟩ := HistoryDifference.PairProof.pairUpperSector n p tag ht (ctx+1) B (.var 0)
  have hh : Hilbert.Local T (ctx+1) [H] (.equal A E) := .hypothesis List.mem_cons_self
  have hr : Derivation T (.imp (.equal E A) (.imp (upperValue tag E B) (upperValue tag A B))) := by
    have d := Derivation.logical (A := T)
      (.equalityReplace (upperValue tag (.var 0) (liftTerm B)) E A)
    rwa [GorbowPACore.logicalFormula,upperValueAt,upperValueAt] at d
  have hout : Hilbert.Local T (ctx+1) [H] (upperValue tag A B) :=
    .mp (.mp (.base hr) (localSym A E hh)) (.base hsector)
  have hbody : Derivation T (.imp (upperBody a b) (GorbowPACore.weaken (upperValue tag a b))) := by
    rw [weakenUpperValue]
    exact Hilbert.Local.finish (Hilbert.Local.discharge hout)
  exact HBQuantifier.existentialElimination T (upperBody a b) (upperValue tag a b) ⟨hbody⟩

theorem pairGraph : Targets.PairGraph := by
  intro n p tag ht ctx a b
  let T := GorbowPRNumeralCalculation.Theory p
  obtain ⟨hl⟩ := pairLowerOrder n p tag ht ctx a b
  obtain ⟨hu⟩ := pairUpperOrder n p tag ht ctx a b
  obtain ⟨hs⟩ := SplitProof.additiveSplit T ctx a b
  have hleft : Derivation T (.imp (lower a b) (HistoryOrder.pairGraph tag a b)) := by
    have h : Hilbert.Local T ctx [lower a b] (lower a b) := .hypothesis List.mem_cons_self
    have hv := Hilbert.Local.mp (.base hl) h
    have hc : Hilbert.Local T ctx [lower a b] (.conj (lower a b) (lowerValue tag a b)) :=
      .mp (.mp (.base (.logical (.andIntro _ _))) h) hv
    exact Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (.logical (.orLeft _ _))) hc))
  have hright : Derivation T (.imp (upper a b) (HistoryOrder.pairGraph tag a b)) := by
    have h : Hilbert.Local T ctx [upper a b] (upper a b) := .hypothesis List.mem_cons_self
    have hv := Hilbert.Local.mp (.base hu) h
    have hc : Hilbert.Local T ctx [upper a b] (.conj (upper a b) (upperValue tag a b)) :=
      .mp (.mp (.base (.logical (.andIntro _ _))) h) hv
    exact Hilbert.Local.finish (Hilbert.Local.discharge (.mp (.base (.logical (.orRight _ _))) hc))
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hleft) hright) hs⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder.PairProof
