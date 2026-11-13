module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.WitnessProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ShellSuccessorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.SectorSplitProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ImageSuccessorProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport WitnessProof

noncomputable def successorSecond {T : Sentence → Prop} {ctx : Nat} {G : List (Formula ctx)}
    tag (a b c : Term ctx) (h : Hilbert.Local T ctx G (.equal b c)) :
    Hilbert.Local T ctx G (.equal (.succ (HistoryKernel.pairCall tag a b))
      (.succ (HistoryKernel.pairCall tag a c))) := by
  have he := localUnary (.succ (HistoryKernel.pairCall tag (liftTerm a) (.var 0))) b c h
  simpa only [substitute,substPair,liftTerm,Support.shiftCancel,Fin.cases_zero] using he

theorem lowerImage {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.lower a b) (pairSurjective tag (.succ (HistoryKernel.pairCall tag a b))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := HistoryOrder.lower a b
  let E := Formula.equal b (.succ a)
  let J := HistoryOrder.lower (.succ a) b
  let Q := pairSurjective tag (.succ (HistoryKernel.pairCall tag a b))
  obtain ⟨hs⟩ := SectorSplitProof.lowerNext T a b
  obtain ⟨hb⟩ := ShellSuccessorProof.lowerBoundary p tag ht a
  obtain ⟨hi⟩ := ShellSuccessorProof.lowerInterior p tag ht a b
  have he : Hilbert.Local T ctx [E,H] E := .hypothesis List.mem_cons_self
  have hc := successorSecond tag a b (.succ a) he
  have hboundary : Hilbert.Local T ctx [E,H] Q :=
    .mp (.base (witnessIntro tag (.succ a) .zero _))
      (localTrans _ _ _ (.base hb) (HistoryOrder.StepProof.localSym _ _ hc))
  have hj : Hilbert.Local T ctx [J,H] J := .hypothesis List.mem_cons_self
  have hh : Hilbert.Local T ctx [J,H] H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hinterior : Hilbert.Local T ctx [J,H] Q :=
    .mp (.base (witnessIntro tag (.succ a) b _)) (.mp (.mp (.base hi) hh) hj)
  have hsplit : Hilbert.Local T ctx [H] (.disj E J) :=
    .mp (.base hs) (.hypothesis List.mem_cons_self)
  have hout : Hilbert.Local T ctx [H] Q :=
    .mp (.mp (.mp (.base (.logical (.orElim E J Q)))
      (Hilbert.Local.discharge hboundary)) (Hilbert.Local.discharge hinterior)) hsplit
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

theorem upperImage {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.imp (HistoryOrder.upper a b) (pairSurjective tag (.succ (HistoryKernel.pairCall tag a b))))) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let H := HistoryOrder.upper a b
  let E := Formula.equal a b
  let J := HistoryOrder.upper a (.succ b)
  let Q := pairSurjective tag (.succ (HistoryKernel.pairCall tag a b))
  obtain ⟨hs⟩ := SectorSplitProof.upperNext T a b
  obtain ⟨hb⟩ := ShellSuccessorProof.upperBoundary p tag ht a
  obtain ⟨hi⟩ := ShellSuccessorProof.upperInterior p tag ht a b
  have he : Hilbert.Local T ctx [E,H] E := .hypothesis List.mem_cons_self
  have hc := successorSecond tag a b a (HistoryOrder.StepProof.localSym _ _ he)
  have hboundary : Hilbert.Local T ctx [E,H] Q :=
    .mp (.base (witnessIntro tag .zero (.succ a) _))
      (localTrans _ _ _ (.base hb) (HistoryOrder.StepProof.localSym _ _ hc))
  have hj : Hilbert.Local T ctx [J,H] J := .hypothesis List.mem_cons_self
  have hh : Hilbert.Local T ctx [J,H] H := .hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)
  have hinterior : Hilbert.Local T ctx [J,H] Q :=
    .mp (.base (witnessIntro tag a (.succ b) _)) (.mp (.mp (.base hi) hh) hj)
  have hsplit : Hilbert.Local T ctx [H] (.disj E J) :=
    .mp (.base hs) (.hypothesis List.mem_cons_self)
  have hout : Hilbert.Local T ctx [H] Q :=
    .mp (.mp (.mp (.base (.logical (.orElim E J Q)))
      (Hilbert.Local.discharge hboundary)) (Hilbert.Local.discharge hinterior)) hsplit
  exact ⟨Hilbert.Local.finish (Hilbert.Local.discharge hout)⟩

/-- Every actual pair image has a successor image, by exhaustive PA sectors. -/
theorem imageSuccessor {n ctx : Nat} (p : Program n) tag
    (ht : (nodes p)[tag]? = some ⟨2,HistoryCodec.pair⟩) (a b : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (pairSurjective tag (.succ (HistoryKernel.pairCall tag a b)))) := by
  obtain ⟨hl⟩ := lowerImage p tag ht a b
  obtain ⟨hu⟩ := upperImage p tag ht a b
  obtain ⟨hs⟩ := HistoryOrder.SplitProof.additiveSplit (GorbowPRNumeralCalculation.Theory p) ctx a b
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hl) hu) hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryIteratorSuffix.ImageSuccessorProof
