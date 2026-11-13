module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.InitialProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof List.Vector
open SixSol20261112.Fuel NamedArithmeticGraph HistoryRuleSuffix

theorem internalBound : Targets.InternalBound := by
  intro n p tag ht ctx certificate
  exact Equations.projection p tag (0 : Fin 1) ht (certificate ::ᵥ nil)

def initialArguments : Fin 2 → Program 1 := Fin.cases (constant 1 1) (Fin.cases (.projection 0) Fin.elim0)

theorem internalInitial : Targets.InternalInitial := by
  intro n p tag ptag ht hp ctx certificate
  have hconst := Equations.argumentChild p tag HistoryCodec.pair initialArguments ht 0
  have hproj := Equations.argumentChild p tag HistoryCodec.pair initialArguments ht 1
  have hpair := Equations.functionChild p tag HistoryCodec.pair initialArguments ht
  obtain ⟨he⟩ := HistoryAppend.ValueEquationsProof.binaryValues p tag HistoryCodec.pair initialArguments ht
    (certificate ::ᵥ nil) (.succ .zero) certificate
    (HistoryKernel.EqualEquationsProof.oneEquation p _ hconst _)
    (Equations.projection p _ (0 : Fin 1) hproj _)
  obtain ⟨hc⟩ := HistoryDecoder.PairCongruenceProof.pairCopies p (tag+1) ptag hpair hp (.succ (.zero : Term ctx)) certificate
  exact ⟨Logic.trans _ _ _ he hc⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCheckerAuxiliaries.InitialProof
