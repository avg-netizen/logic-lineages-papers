module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.GuardProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.SuffixProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowSubstitution List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof

noncomputable def mpLeftCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (n raw a a' b : Term ctx) (h : Hilbert.Local T ctx G (.equal a a')) :
    Hilbert.Local T ctx G (.equal (call tag (n ::ᵥ raw ::ᵥ a ::ᵥ b ::ᵥ nil))
      (call tag (n ::ᵥ raw ::ᵥ a' ::ᵥ b ::ᵥ nil))) := by
  have d := localUnary (call tag (liftTerm n ::ᵥ liftTerm raw ::ᵥ .var 0 ::ᵥ liftTerm b ::ᵥ nil)) a a' h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d
noncomputable def mpRightCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (n raw a b b' : Term ctx) (h : Hilbert.Local T ctx G (.equal b b')) :
    Hilbert.Local T ctx G (.equal (call tag (n ::ᵥ raw ::ᵥ a ::ᵥ b ::ᵥ nil))
      (call tag (n ::ᵥ raw ::ᵥ a ::ᵥ b' ::ᵥ nil))) := by
  have d := localUnary (call tag (liftTerm n ::ᵥ liftTerm raw ::ᵥ liftTerm a ::ᵥ .var 0 ::ᵥ nil)) b b' h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d
noncomputable def generalizeCongruence {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (n raw a a' : Term ctx) (h : Hilbert.Local T ctx G (.equal a a')) :
    Hilbert.Local T ctx G (.equal (call tag (n ::ᵥ raw ::ᵥ a ::ᵥ nil))
      (call tag (n ::ᵥ raw ::ᵥ a' ::ᵥ nil))) := by
  have d := localUnary (call tag (liftTerm n ::ᵥ liftTerm raw ::ᵥ .var 0 ::ᵥ nil)) a a' h
  simpa only [Logic.substCall,List.Vector.map_cons,List.Vector.map_nil,liftTerm,Support.shiftCancel,substitute,Fin.cases_zero] using d

noncomputable def reject {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    (value : Term ctx) (Q : Formula ctx)
    (hone : Hilbert.Local T ctx G (.equal value (.succ .zero)))
    (hzero : Hilbert.Local T ctx G (.equal value .zero)) : Hilbert.Local T ctx G Q :=
  Hilbert.Local.explosion Q (localTrans _ _ _ (HistoryOrder.StepProof.localSym _ _ hone) hzero)
    (.base (.arithmetic (.succNotZero .zero)))

theorem internalGeneralizeSuffix : Targets.InternalGeneralizeSuffix := by
  intro arity p tag atag ht ha ctx h tail n raw r
  let T := GorbowPRNumeralCalculation.Theory p
  let a := HistoryLookup.lookupCall (generalizeLookupTag tag) r h
  let a' := HistoryLookup.lookupCall (generalizeLookupTag tag) r (HistoryAppend.appendCall atag h tail)
  let E := Formula.equal (generalizeCall tag h n raw r) (.succ .zero)
  let Q := Formula.equal (generalizeCall tag (HistoryAppend.appendCall atag h tail) n raw r) (.succ .zero)
  let Z := Formula.equal a .zero
  let S := Formula.equal a' a
  obtain ⟨hb,hl⟩ := generalizeNodes p tag ht
  obtain ⟨old⟩ := generalizeEquation p tag ht h n raw r
  obtain ⟨new⟩ := generalizeEquation p tag ht (HistoryAppend.appendCall atag h tail) n raw r
  obtain ⟨hz⟩ := GuardProof.generalizeZero p (tag+1) hb n raw
  obtain ⟨split⟩ := ReferenceCasesProof.lookupCases p atag (generalizeLookupTag tag) ha hl r h tail
  have zeroBranch : Hilbert.Local T ctx [E] (.imp Z Q) := by
    have he : Hilbert.Local T ctx [Z,E] E := .hypothesis (by simp)
    have hza : Hilbert.Local T ctx [Z,E] Z := .hypothesis List.mem_cons_self
    have hone := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
    have hzero := localTrans _ _ _ (generalizeCongruence (tag+1) n raw a .zero hza) (.base hz)
    exact Hilbert.Local.discharge (reject _ Q hone hzero)
  have stableBranch : Hilbert.Local T ctx [E] (.imp S Q) := by
    have he : Hilbert.Local T ctx [S,E] E := .hypothesis (by simp)
    have hs : Hilbert.Local T ctx [S,E] S := .hypothesis List.mem_cons_self
    have hone := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
    have heq := generalizeCongruence (tag+1) n raw a' a hs
    exact Hilbert.Local.discharge (localTrans _ _ _ (.base new) (localTrans _ _ _ heq hone))
  have out : Hilbert.Local T ctx [E] Q :=
    .mp (.mp (.mp (.base (.logical (.orElim Z S Q))) zeroBranch) stableBranch) (.base split)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge out)⟩

theorem internalMPSuffix : Targets.InternalMPSuffix := by
  intro arity p tag atag ht ha ctx h tail n raw r1 r2
  let T := GorbowPRNumeralCalculation.Theory p
  let a := HistoryLookup.lookupCall (mpLeftTag tag) r1 h
  let b := HistoryLookup.lookupCall (mpRightTag tag) r2 h
  let a' := HistoryLookup.lookupCall (mpLeftTag tag) r1 (HistoryAppend.appendCall atag h tail)
  let b' := HistoryLookup.lookupCall (mpRightTag tag) r2 (HistoryAppend.appendCall atag h tail)
  let E := Formula.equal (mpCall tag h n raw r1 r2) (.succ .zero)
  let Q := Formula.equal (mpCall tag (HistoryAppend.appendCall atag h tail) n raw r1 r2) (.succ .zero)
  let ZA := Formula.equal a .zero
  let ZB := Formula.equal b .zero
  let SA := Formula.equal a' a
  let SB := Formula.equal b' b
  obtain ⟨hb,hla,hlb⟩ := mpNodes p tag ht
  obtain ⟨old⟩ := mpEquation p tag ht h n raw r1 r2
  obtain ⟨new⟩ := mpEquation p tag ht (HistoryAppend.appendCall atag h tail) n raw r1 r2
  obtain ⟨hza⟩ := GuardProof.mpZeroLeft p (tag+1) hb n raw b
  obtain ⟨hzb⟩ := GuardProof.mpZeroRight p (tag+1) hb n raw a
  obtain ⟨splitA⟩ := ReferenceCasesProof.lookupCases p atag (mpLeftTag tag) ha hla r1 h tail
  obtain ⟨splitB⟩ := ReferenceCasesProof.lookupCases p atag (mpRightTag tag) ha hlb r2 h tail
  have zeroA : Hilbert.Local T ctx [E] (.imp ZA Q) := by
    have he : Hilbert.Local T ctx [ZA,E] E := .hypothesis (by simp)
    have hz : Hilbert.Local T ctx [ZA,E] ZA := .hypothesis List.mem_cons_self
    have hone := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
    have hzero := localTrans _ _ _ (mpLeftCongruence (tag+1) n raw a .zero b hz) (.base hza)
    exact Hilbert.Local.discharge (reject _ Q hone hzero)
  have stableA : Hilbert.Local T ctx [E] (.imp SA Q) := by
    have zeroB : Hilbert.Local T ctx [SA,E] (.imp ZB Q) := by
      have he : Hilbert.Local T ctx [ZB,SA,E] E := .hypothesis (by simp)
      have hz : Hilbert.Local T ctx [ZB,SA,E] ZB := .hypothesis List.mem_cons_self
      have hone := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
      have hzero := localTrans _ _ _ (mpRightCongruence (tag+1) n raw a b .zero hz) (.base hzb)
      exact Hilbert.Local.discharge (reject _ Q hone hzero)
    have stableB : Hilbert.Local T ctx [SA,E] (.imp SB Q) := by
      have he : Hilbert.Local T ctx [SB,SA,E] E := .hypothesis (by simp)
      have hsa : Hilbert.Local T ctx [SB,SA,E] SA := .hypothesis (by simp)
      have hsb : Hilbert.Local T ctx [SB,SA,E] SB := .hypothesis List.mem_cons_self
      have hone := localTrans _ _ _ (.base (Support.equalitySymmetry _ _ old)) he
      have hc := localTrans _ _ _ (mpLeftCongruence (tag+1) n raw a' a b' hsa)
        (mpRightCongruence (tag+1) n raw a b' b hsb)
      exact Hilbert.Local.discharge (localTrans _ _ _ (.base new) (localTrans _ _ _ hc hone))
    exact Hilbert.Local.discharge
      (.mp (.mp (.mp (.base (.logical (.orElim ZB SB Q))) zeroB) stableB) (.base splitB))
  have out : Hilbert.Local T ctx [E] Q :=
    .mp (.mp (.mp (.base (.logical (.orElim ZA SA Q))) zeroA) stableA) (.base splitA)
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge out)⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryRuleSuffix.SuffixProof
