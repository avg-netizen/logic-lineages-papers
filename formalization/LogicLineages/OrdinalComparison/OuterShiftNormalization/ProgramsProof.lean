module
public import LogicLineages.OrdinalComparison.OuterShiftNormalization.Targets
public import LogicLineages.OrdinalComparison.TerminalWordGrowthCompletion.ProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
open PolynomialGraphCompletion WordGuardCompletion

theorem splitStep_primitive :
    Primrec (fun p : Letter × (Word × Word) => splitStep p.1 p.2) := by
  have ha : Primrec (fun p : Letter × (Word × Word) => p.1) := Primrec.fst
  have hc : Primrec (fun p : Letter × (Word × Word) => p.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun p : Letter × (Word × Word) => p.2.2) :=
    Primrec.snd.comp Primrec.snd
  have htest : PrimrecPred (fun p : Letter × (Word × Word) =>
      p.2.1 = [] ∧ p.1.1 = 0) :=
    (Primrec.eq.comp hc (Primrec.const [])).and
      (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.const 0))
  exact Primrec.ite htest
    ((Primrec.const []).pair (Primrec.list_cons.comp ha hs))
    ((Primrec.list_cons.comp ha hc).pair hs)

theorem splitWord_primitive : Primrec splitWord :=
  Primrec.list_foldr Primrec.id (Primrec.const ([], []))
    (splitStep_primitive.comp Primrec.snd).to₂

theorem coreWord_primitive : Primrec coreWord :=
  Primrec.fst.comp splitWord_primitive

theorem shiftSuffix_primitive : Primrec shiftSuffix :=
  Primrec.snd.comp splitWord_primitive

theorem shiftSum_primitive : Primrec shiftSum := by
  have hs : Primrec (fun p : Letter × Int => p.1.2.2.2 + p.2) :=
    LayeredComparison.IntegerAlgorithms.Proof.add_primitive.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const (0 : Int))
    (hs.comp Primrec.snd).to₂

theorem outerShift_primitive : Primrec outerShift :=
  shiftSum_primitive.comp shiftSuffix_primitive

theorem normalizedWord_primitive : Primrec normalizedWord := by
  have hs : Primrec shiftLetter :=
    (Primrec.const 0).pair
      ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))
  exact Primrec.list_append.comp coreWord_primitive
    (Primrec.list_cons.comp (hs.comp outerShift_primitive) (Primrec.const []))

theorem leafPairTail_primitive :
    Primrec (fun p : Word × Word => leafPairTail p.1 p.2) :=
  Primrec.nat_max.comp
    (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.fst)
    (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.snd)

theorem nonlinearLeafTail_primitive :
    Primrec (fun p : Word × Word => nonlinearLeafTail p.1 p.2) :=
  Primrec.nat_max.comp
    (TerminalWordGrowthCompletion.Proof.terminalTail_primitive.comp
      (Primrec.fst.pair (shiftSum_primitive.comp Primrec.snd)))
    (WordGuardCompletion.Proof.wordTail_primitive.comp Primrec.snd)

theorem normalizationPrograms : Targets.NormalizationPrograms :=
  ⟨splitWord_primitive, coreWord_primitive, shiftSuffix_primitive, shiftSum_primitive,
    outerShift_primitive, normalizedWord_primitive, leafPairTail_primitive,
    nonlinearLeafTail_primitive⟩

end LogicLineages.OrdinalComparison.OuterShiftNormalization.Proof
