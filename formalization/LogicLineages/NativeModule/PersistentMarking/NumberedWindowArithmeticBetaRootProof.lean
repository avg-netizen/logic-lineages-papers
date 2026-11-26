module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticFreshRootProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticSingletonChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRawContextFocusProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticBetaRootProof
open NumberedWindowArithmeticBinderRootTargets NumberedWindowBinderRootAlgorithm
open NumberedWindowRawWitnessRootBits NumberedWindowSyntax NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode NumberedWindowRawContextFrameView
open NumberedWindowArithmeticRootComparisonProof NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticFreshRootProof (parse)

private theorem instanceCode (a body : NTerm) :
    (NumberedWindowSingletonAlgorithm.output (encodeTerm a) 0 (encodeTerm body)).1 =
      some (encodeTerm (substitute (.cons a .nil) 0 body)) := by
  rw [NumberedWindowArithmeticSingletonChecks.exact_ExactSingletonOutput]
  simp [exact_TermCodec.2.1]

theorem betaExact : ExactBetaRoot := by
  intro S K
  funext a b
  apply onCodes
  intro q r
  simp only [parse,Option.any_some]
  cases q with
  | auxApp σ τ fn a =>
    simp only [view,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,List.getElem?_cons_zero,
      Option.getD_some,parse,Option.any_some]
    cases fn <;> try rfl
    rename_i ρ b
    change ((encodeTy σ == encodeTy ρ) &&
      ((NumberedWindowSingletonAlgorithm.output (encodeTerm a) 0 (encodeTerm b)).1).any
        (· == encodeTerm r)) = _
    rw [instanceCode,NumberedWindowRawContextFocusProof.typeEq]
    exact congrArg (fun v => decide (σ = ρ) && v)
      (NumberedWindowArithmeticExchangeAtomsChecks.exact_LiteralEquality.1 _ _)
  | _ =>
    cases NumberedWindowFieldAlgorithm.unpackNode _ <;> rfl
end LogicLineages.PersistentMarking.NumberedWindowArithmeticBetaRootProof
