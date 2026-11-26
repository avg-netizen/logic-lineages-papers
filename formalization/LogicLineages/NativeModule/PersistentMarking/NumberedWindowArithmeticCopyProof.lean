module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticCopyRankProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticOwnerChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticRootComparisonProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticExchangeAtomsChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyProof
open NumberedWindowCopyAlgorithm NumberedWindowArithmeticCopyTargets NumberedWindowArithmeticCopyRankProof
open NumberedWindowSyntax NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode
open NumberedWindowArithmeticRootComparisonProof NumberedWindowRawWitnessRootBits NumberedWindowAdmissionTargets

private def fields : NTerm → Nat × List Nat
  | .free σ x => (0,[encodeTy σ,x])
  | .bound σ i => (1,[encodeTy σ,i])
  | .lam σ q => (2,[encodeTy σ,encodeTerm q])
  | .bottom σ => (3,[encodeTy σ])
  | .ordinary f bs => (4,[encodeHead f,encodeArgs bs])
  | .numbered f τ k bs es => (5,[encodeHead f,encodeTy τ,k,encodeArgs bs,encodeArgs es])
  | .auxApp σ τ q a => (6,[encodeTy σ,encodeTy τ,encodeTerm q,encodeTerm a])

private theorem parse (q : NTerm) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeTerm q) = some (fields q) := by
  cases q <;> exact readNode _ _

theorem copyExact : ExactCopyRoot := by
  intro S K
  funext a b
  apply onCodes
  intro q r
  simp only [parse,Option.any_some]
  cases q with
  | numbered f τ k bs es =>
    cases k with
    | zero => cases r <;> rfl
    | succ k =>
      cases r <;> try rfl
      rename_i g target
      change (allowedTarget true S.entries (window S K).2 (encodeTy τ) (encodeHead f) (encodeHead g) &&
        NumberedWindowOwnerAlgorithm.copies (encodeHead f) k (encodeArgs bs) (encodeArgs es)
          (NumberedWindowAnnotationAlgorithm.declaration (encodeHead g)).2 == encodeArgs target) = _
      rw [allowedExact,NumberedWindowArithmeticAnnotationProof.head,
        NumberedWindowArithmeticOwnerChecks.exact_ExactOwnerCopies,
        NumberedWindowArithmeticExchangeAtomsChecks.exact_LiteralEquality.2]
      rfl
  | _ => rfl
end LogicLineages.PersistentMarking.NumberedWindowArithmeticCopyProof
