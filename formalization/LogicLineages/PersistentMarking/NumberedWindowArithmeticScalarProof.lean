import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticCoverBoundsChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticClassAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticLexicalChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowAdmissionChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAddressAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarProof
open Spine NumberedWindowTypingBits NumberedWindowScalarAlgorithm NumberedWindowArithmeticScalarTargets
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticClassAlgorithmTargets NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticHeadCode NumberedWindowSyntax

private theorem admittedEq (S K Γ τ n) :
    admitted (fixed S K) (Γ.map encodeTy) (encodeTy τ) n = (decodeTerm n).any (finiteWindowBit S K Γ τ) := by
  unfold admitted
  rw [NumberedWindowArithmeticLexicalChecks.exact_ExactFiniteTypedChecker]
  change (_ && (NumberedWindowAdmissionAlgorithm.bits (NumberedWindowAdmissionTargets.window S K) n).1) = _
  rw [NumberedWindowAdmissionChecks.exact_DecodedAdmission]
  cases h : decodeTerm n with
  | none => rfl
  | some q => simp [Option.any,finiteWindowBit,windowBit,NumberedWindowAdmissionTargets.termGuard,
      NumberedWindowAdmissionTargets.typesIn,Bool.and_assoc]

private theorem edgeEq (S K Γ τ a b) : edge (fixed S K) (Γ.map encodeTy) (encodeTy τ) a b =
    codedExchange S K Γ τ a b := by
  unfold edge codedExchange
  rw [admittedEq,admittedEq]
  change ((NumberedWindowExchangeAlgorithm.bits (NumberedWindowArithmeticExchangeAtomsTargets.pairs S K) a b).1 && _ && _) = _
  rw [NumberedWindowArithmeticExchangeChecks.exact_DecodedContextualExchange]
  cases h : decodeTerm a <;> cases k : decodeTerm b <;> rfl

theorem guarded : ExactGuardedExchange := fun S K Γ τ => ⟨admittedEq S K Γ τ,edgeEq S K Γ τ⟩

private theorem verticesEq (S K n) : vertices (fixed S K) n =
    ((decodeTerm n).map (fun q => (NumberedWindowPrimaryCoverSyntax.cover S K q).map encodeTerm)).getD [] := by
  exact congrArg (fun o => o.getD []) (NumberedWindowArithmeticCoverBoundsChecks.exact_SourceSelectedCover S K n)

theorem leastEq : ExactLeastRepresentative := by
  intro S K Γ τ n
  unfold NumberedWindowScalarAlgorithm.least
  rw [show edge (fixed S K) (Γ.map encodeTy) (encodeTy τ) = codedExchange S K Γ τ from
    funext (fun a => funext (edgeEq S K Γ τ a)),verticesEq]
  cases h : decodeTerm n with
  | none => rfl
  | some q =>
    have he := (exact_TermCodec.1 n q).mp h
    simpa only [← he,Option.map_some,Option.getD_some,Option.bind_some] using
      (NumberedWindowArithmeticClassAlgorithmChecks.exact_ExactPrimaryListAndLeast S K Γ τ q).2

private theorem canonicalEq (S K) (a : ClassAddress) :
    canonical (fixed S K) (NumberedWindowArithmeticAddressAlgorithmTargets.address a) = canonicalBit S K a := by
  unfold canonical canonicalBit NumberedWindowArithmeticAddressAlgorithmTargets.address
  simp only [admittedEq]
  rw [leastEq S K a.context a.result a.least]
  cases h : decodeTerm a.least with
  | none => rfl
  | some q =>
    have same : (leastCode S K a.context a.result q == some a.least) =
        decide (leastCode S K a.context a.result q = some a.least) :=
      Bool.eq_iff_iff.mpr (by simp)
    simp [Option.any,same]

theorem scalarEq : ExactScalarAddress := by
  intro S K
  funext n
  unfold scalar addressBit
  rw [NumberedWindowArithmeticAddressAlgorithmChecks.exact_ExactAddressView]
  cases h : decodeAddress n with
  | none => rfl
  | some a => exact canonicalEq S K a

end LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarProof
