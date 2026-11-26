module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.EquationsProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.FailureProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph FieldsProof EquationsProof
open HistoryKernel.TransitionEquationsProof (threeValues)

theorem noneEquation {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (finalCall tag (HistoryKernel.pairCall ptag .zero lines) requested formula certificate) .zero)) := by
  let av := args ptag .zero lines requested formula certificate
  let raw := call (historyTag tag) av
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select outerArguments ht av .zero .zero raw
    (optionEquation p _ ptag (Equations.argumentChild p tag HistoryCodec.select outerArguments ht 0) hp .zero lines requested formula certificate)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p tag HistoryCodec.select outerArguments ht 1) av)
    ⟨.logical (.reflexive _)⟩
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (tag+1)
    (Equations.functionChild p tag HistoryCodec.select outerArguments ht) (.zero : Term ctx) raw
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem emptyHistory {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (call (historyTag tag) (args ptag (.succ .zero) lines requested formula certificate)) .zero)) := by
  let av := args ptag (.succ .zero) lines requested formula certificate
  let raw := call (checksTag tag) av
  have hh := historyInstalled p tag ht
  obtain ⟨he⟩ := threeValues p (historyTag tag) HistoryCodec.select historyArguments hh av .zero .zero raw
    (FieldsProof.historyEquation p _ ptag (Equations.argumentChild p _ HistoryCodec.select historyArguments hh 0) hp .zero lines requested formula certificate)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p _ HistoryCodec.select historyArguments hh 1) av)
    ⟨.logical (.reflexive _)⟩
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectZero p (historyTag tag+1)
    (Equations.functionChild p _ HistoryCodec.select historyArguments hh) (.zero : Term ctx) raw
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem emptyEquation {n ctx : Nat} (p : Program n) (tag ptag : Nat)
    (ht : (nodes p)[tag]? = some ⟨4,finalizer⟩)
    (hp : (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩) (lines requested formula certificate : Term ctx) :
    Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
      (.equal (finalCall tag (HistoryKernel.pairCall ptag (.succ .zero) lines) requested formula certificate) .zero)) := by
  let av := args ptag (.succ .zero) lines requested formula certificate
  obtain ⟨he⟩ := threeValues p tag HistoryCodec.select outerArguments ht av (.succ .zero) .zero .zero
    (optionEquation p _ ptag (Equations.argumentChild p tag HistoryCodec.select outerArguments ht 0) hp (.succ .zero) lines requested formula certificate)
    (HistoryAppend.TableEquationsProof.zeroEquation p _ (Equations.argumentChild p tag HistoryCodec.select outerArguments ht 1) av)
    (emptyHistory p tag ptag ht hp lines requested formula certificate)
  obtain ⟨hs⟩ := HistoryCodec.PairProof.selectPositive p (tag+1)
    (Equations.functionChild p tag HistoryCodec.select outerArguments ht) (.zero : Term ctx) .zero .zero
  exact ⟨Logic.trans _ _ _ he hs⟩

theorem internalFinishFailure : Targets.InternalFinishFailure := by
  intro n p tag ptag ht hp ctx lines requested formula certificate
  obtain ⟨hn⟩ := noneEquation p tag ptag ht hp lines requested formula certificate
  obtain ⟨he⟩ := emptyEquation p tag ptag ht hp lines requested formula certificate
  exact ⟨.mp (.mp (.logical (.andIntro _ _)) hn) he⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.FailureProof
