module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.ShapeProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CasesProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowSubstitution GorbowFormulaSubstitution
open SixSol20261112.Fuel NamedArithmeticGraph LiteralCheckerAuxiliaries WitnessProof ShapeProof
open HistoryCodec.ArithmeticSupport HistoryIteratorSuffix.WitnessProof HistoryKernel

theorem entrySound {n ctx : Nat} (p : Program n) (ftag dtag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (entry tail lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (sound ftag dtag ptag ctag (pairCall ptag (.succ (pairCall ctag entry tail)) lines) requested formula certificate)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := sound ftag dtag ptag ctag (pairCall ptag (.succ (pairCall ctag entry tail)) lines) requested formula certificate
  let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm entry)
  let C := liftTerm (liftTerm entry)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall ptag A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨hi⟩ := successful p ftag dtag ptag ctag hf hd hp hc A B
    (liftTerm (liftTerm tail)) (liftTerm (liftTerm lines)) (liftTerm (liftTerm requested))
    (liftTerm (liftTerm formula)) (liftTerm (liftTerm certificate))
  have hhistory := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ctag _ (liftTerm (liftTerm tail)) _ (liftTerm (liftTerm tail)) hh (.base (.logical (.reflexive _)))
  have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ (liftTerm (liftTerm lines)) _ (liftTerm (liftTerm lines))
    (localUnary (.succ (.var 0)) _ _ hhistory) (.base (.logical (.reflexive _)))
  have hout := Hilbert.Local.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _
    (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula)) (liftTerm (liftTerm certificate)))) hs) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenSound,successfulState,liftTerm,renameTerm,substPair,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody ptag entry) Q ⟨hinner⟩
  obtain ⟨he⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p ptag hp ctx entry
  exact ⟨.mp helim he⟩

theorem positiveHistory {n ctx : Nat} (p : Program n) (ftag dtag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (code lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (sound ftag dtag ptag ctag (pairCall ptag (.succ (.succ code)) lines) requested formula certificate)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let cp := ctag + GorbowPRChildTags.argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  let Q := sound ftag dtag ptag ctag (pairCall ptag (.succ (.succ code)) lines) requested formula certificate
  let H := secondBody cp (.var (0 : Fin (ctx+1))) (liftTerm code)
  let C := liftTerm (liftTerm code)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall cp A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨he⟩ := HistoryCodec.PairProof.internalCons n p ctag hc (ctx+2) A B
  have hcons := localTrans _ _ _ (.base he) (localUnary (.succ (.var 0)) _ _ hh)
  have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ (liftTerm (liftTerm lines)) _ (liftTerm (liftTerm lines))
    (localUnary (.succ (.var 0)) _ _ hcons) (.base (.logical (.reflexive _)))
  obtain ⟨hi⟩ := entrySound p ftag dtag ptag ctag hf hd hp hc A B
    (liftTerm (liftTerm lines)) (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula)) (liftTerm (liftTerm certificate))
  have hout := Hilbert.Local.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _
    (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula)) (liftTerm (liftTerm certificate)))) hs) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenSound,liftTerm,renameTerm,substPair,substitute] using
      Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody cp code) Q ⟨hinner⟩
  obtain ⟨he⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p cp hcp ctx code
  exact ⟨.mp helim he⟩

theorem historySound {n ctx : Nat} (p : Program n) (ftag dtag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (history lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (sound ftag dtag ptag ctag (pairCall ptag (.succ history) lines) requested formula certificate)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := sound ftag dtag ptag ctag (pairCall ptag (.succ history) lines) requested formula certificate
  let E := Formula.equal history .zero
  obtain ⟨hz⟩ := FailureProof.emptyEquation p ftag ptag hf hp lines requested formula certificate
  obtain ⟨hr⟩ := rejected ftag dtag ptag ctag _ requested formula certificate hz
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hopt : Hilbert.Local T ctx [E] (.equal (.succ .zero) (.succ history)) := localUnary (.succ (.var 0)) _ _ (HistoryOrder.StepProof.localSym _ _ he)
  have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ lines _ lines hopt (.base (.logical (.reflexive lines)))
  have hzq : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _ requested formula certificate)) hs) (.base hr)))
  let H := HistoryOrder.SupportProof.predBody history
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm history) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := positiveHistory p ftag dtag ptag ctag hf hd hp hc (.var (0 : Fin (ctx+1)))
    (liftTerm lines) (liftTerm requested) (liftTerm formula) (liftTerm certificate)
  have hop : Hilbert.Local T (ctx+1) [H] (.equal (.succ (.succ (.var 0))) (.succ (liftTerm history))) := localUnary (.succ (.var 0)) _ _ (HistoryOrder.StepProof.localSym _ _ hh)
  have hstate := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ (liftTerm lines) _ (liftTerm lines) hop (.base (.logical (.reflexive _)))
  have hout := Hilbert.Local.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _
    (liftTerm requested) (liftTerm formula) (liftTerm certificate))) hstate) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenSound,liftTerm,renameTerm,substPair,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hc⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T history
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzq) hpos) hc⟩

theorem optionSound {n ctx : Nat} (p : Program n) (ftag dtag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (option lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (sound ftag dtag ptag ctag (pairCall ptag option lines) requested formula certificate)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := sound ftag dtag ptag ctag (pairCall ptag option lines) requested formula certificate
  let E := Formula.equal option .zero
  obtain ⟨hz⟩ := FailureProof.noneEquation p ftag ptag hf hp lines requested formula certificate
  obtain ⟨hr⟩ := rejected ftag dtag ptag ctag _ requested formula certificate hz
  have he : Hilbert.Local T ctx [E] E := .hypothesis List.mem_cons_self
  have hopt : Hilbert.Local T ctx [E] (.equal .zero option) := HistoryOrder.StepProof.localSym _ _ he
  have hs := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ lines _ lines hopt (.base (.logical (.reflexive lines)))
  have hzq : Derivation T (.imp E Q) := Hilbert.Local.finish (Hilbert.Local.discharge
    (.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _ requested formula certificate)) hs) (.base hr)))
  let H := HistoryOrder.SupportProof.predBody option
  have hh : Hilbert.Local T (ctx+1) [H] (.equal (liftTerm option) (.succ (.var 0))) := .hypothesis List.mem_cons_self
  obtain ⟨hn⟩ := historySound p ftag dtag ptag ctag hf hd hp hc (.var (0 : Fin (ctx+1)))
    (liftTerm lines) (liftTerm requested) (liftTerm formula) (liftTerm certificate)
  have hop : Hilbert.Local T (ctx+1) [H] (.equal (.succ (.var 0)) (liftTerm option)) := HistoryOrder.StepProof.localSym _ _ hh
  have hstate := HistoryIteratorSuffix.StepSuffixProof.pairCongruence ptag _ (liftTerm lines) _ (liftTerm lines) hop (.base (.logical (.reflexive _)))
  have hout := Hilbert.Local.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _
    (liftTerm requested) (liftTerm formula) (liftTerm certificate))) hstate) (.base hn)
  have hb : Derivation T (.imp H (GorbowPACore.weaken Q)) := by
    simpa only [Q,weakenSound,liftTerm,renameTerm,substPair,substitute] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hpos⟩ := HBQuantifier.existentialElimination T H Q ⟨hb⟩
  obtain ⟨hc⟩ := HistoryOrder.SupportProof.zeroOrSuccessor T option
  exact ⟨.mp (.mp (.mp (.logical (.orElim _ _ _)) hzq) hpos) hc⟩

theorem allSound {n ctx : Nat} (p : Program n) (ftag dtag ptag ctag : Nat)
    (hf : (nodes p)[ftag]? = some ⟨4,finalizer⟩)
    (hd : (nodes p)[dtag]? = some ⟨1,HistoryDecoder.decoder true⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩)
    (hc : (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩) (state requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (sound ftag dtag ptag ctag state requested formula certificate)) := by
  let T := GorbowPRNumeralCalculation.Theory p
  let Q := sound ftag dtag ptag ctag state requested formula certificate
  let H := secondBody ptag (.var (0 : Fin (ctx+1))) (liftTerm state)
  let C := liftTerm (liftTerm state)
  let A : Term (ctx+2) := .var 1
  let B : Term (ctx+2) := .var 0
  have hh : Hilbert.Local T (ctx+2) [H] (.equal (pairCall ptag A B) C) := .hypothesis List.mem_cons_self
  obtain ⟨hi⟩ := optionSound p ftag dtag ptag ctag hf hd hp hc A B
    (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula)) (liftTerm (liftTerm certificate))
  have hout := Hilbert.Local.mp (.mp (.base (soundTransport ftag dtag ptag ctag _ _
    (liftTerm (liftTerm requested)) (liftTerm (liftTerm formula)) (liftTerm (liftTerm certificate)))) hh) (.base hi)
  have hb : Derivation T (.imp H (GorbowPACore.weaken (GorbowPACore.weaken Q))) := by
    simpa only [Q,C,weakenSound] using Hilbert.Local.finish (Hilbert.Local.discharge hout)
  obtain ⟨hinner⟩ := HBQuantifier.existentialElimination T H (GorbowPACore.weaken Q) ⟨hb⟩
  obtain ⟨helim⟩ := HBQuantifier.existentialElimination T (firstBody ptag state) Q ⟨hinner⟩
  obtain ⟨hs⟩ := HistoryIteratorSuffix.SurjectivityProof.internalPairSurjective n p ptag hp ctx state
  exact ⟨.mp helim hs⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAcceptance.CasesProof
