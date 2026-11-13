module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.ConsCountProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.SaturationProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.ConsProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport EquationsProof SelectProof

theorem internalLengthCons : Targets.InternalLengthCons := by
  intro n p ltag ctag hl hc ctx head tail
  let T := GorbowPRNumeralCalculation.Theory p
  let ct := ltag+1
  let cp := ctag+argumentTag .succ (fun _ : Fin 1 => HistoryCodec.pair) 0
  let code := HistoryLookup.consCall ctag head tail
  let pv := HistoryKernel.pairCall cp head tail
  have hct := Equations.functionChild p ltag count (fun _ : Fin 2 => .projection 0) hl
  have hcp := Equations.argumentChild p ctag .succ (fun _ : Fin 1 => HistoryCodec.pair) hc 0
  obtain ⟨he⟩ := lengthEquation p ltag hl code
  obtain ⟨hcons⟩ := HistoryCodec.PairProof.internalCons n p ctag hc ctx head tail
  have hfirst := countCongruence (T := T) (G := []) ct code (.succ pv) code code (.base hcons) (.base (.logical (.reflexive code)))
  obtain ⟨hshift⟩ := ConsCountProof.countCons p ct ctag hct hc pv head tail
  obtain ⟨hbound⟩ := HistoryBounds.PairProof.pairSecondBound n p cp hcp ctx head tail
  obtain ⟨hsat⟩ := SaturationProof.atLargerBound p ct hct tail pv
  obtain ⟨htail⟩ := lengthEquation p ltag hl tail
  have htailCount : Derivation T (.equal (countCall ct pv tail) (lengthCall ltag tail)) :=
    Logic.trans _ _ _ (.mp hsat hbound) (Support.equalitySymmetry _ _ htail)
  exact ⟨Hilbert.Local.finish (localTrans _ _ _ (.base he)
    (localTrans _ _ _ hfirst (localTrans _ _ _ (.base hshift) (localUnary (.succ (.var 0)) _ _ (.base htailCount)))))⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryLengthOffset.ConsProof
