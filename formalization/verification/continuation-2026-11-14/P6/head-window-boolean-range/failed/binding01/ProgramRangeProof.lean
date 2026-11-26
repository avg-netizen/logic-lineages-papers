module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ContainsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBranchAdequacy.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InductionSyntaxProof
open InternalAcceptanceBranchProof
open InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalPositiveUnfoldingSupportProof InternalQuotientComparisonProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof

def Ranged {m : Nat} (p : Program m) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (out : OTerm alpha)
    (xs : Fin m → OTerm alpha), Nonempty (Derivation body Delta (programGraph p out xs)) →
      Nonempty (Derivation body Delta (BooleanValue out))

theorem constantRange (m : Nat) (bit : Fin 2) : Ranged (constant m bit.val) := by
  intro body alpha Delta out xs h
  obtain ⟨he⟩ := valueUnique (constant m bit.val) out (numeral bit.val) xs h (constantValue bit.val xs)
  have hi : bit.val = 0 ∨ bit.val = 1 := by omega
  rcases hi with hi | hi
  · rw [hi] at he
    exact ⟨orLeft he⟩
  · rw [hi] at he
    exact ⟨orRight he⟩

theorem containsRange : Ranged contains := by
  intro body alpha Delta out xs h
  have hx : Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0) = xs := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  apply ContainsProof.containsRange body alpha Delta (xs 0) (xs 1) out
  change Nonempty (Derivation body Delta (programGraph contains out (Fin.cons (xs 0) (Fin.cons (xs 1) Fin.elim0))))
  rw [hx]
  exact h

theorem compositionRange {m k : Nat} (p : Program k) (g : Fin k → Program m)
    (hp : Ranged p) : Ranged (.composition p g) := by
  intro body alpha Delta out xs h
  apply programCompositionCases p g out xs _ h
  intro beta j ys Theta hj hf hg
  rw [booleanRename]
  exact hp body beta Theta (out.relabel j) ys hf

theorem branchRange {m : Nat} (c a b : Program m) (ha : Ranged a) (hb : Ranged b) :
    Ranged (InternalAcceptance.branch c a b) := by
  intro body alpha Delta out xs hw
  apply programCases c xs _
  intro beta j Theta value hj hc
  rw [booleanRename]
  have hwj := renameInto hw j Theta hj
  rw [programRename] at hwj
  apply zeroSuccessorCases Theta value _
  · have hz : Nonempty (Derivation body (eqn value z :: Theta) (eqn value z)) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hcz := outputTransport c value z (fun i => (xs i).relabel j) hz (withHyp hc (eqn value z))
    exact ha body beta _ (out.relabel j) _
      (zeroBranchElim c a b (out.relabel j) _ hcz (withHyp hwj (eqn value z)))
  · intro gamma k Xi pred hk he
    rw [booleanRename]
    have hck := renameInto hc k Xi hk
    have hwk := renameInto hwj k Xi hk
    simp only [programRename] at hck hwk
    have hcs := outputTransport c (value.relabel k) (suc pred)
      (fun i => ((xs i).relabel j).relabel k) he hck
    exact hb body gamma Xi ((out.relabel j).relabel k) _
      (successorBranchElim c a b ((out.relabel j).relabel k) pred _ hcs hwk)

theorem conjunctionRange {m : Nat} (p q : Program m) (hq : Ranged q) :
    Ranged (InternalAcceptance.conjunction p q) :=
  branchRange p (constant m 0) q (constantRange m 0) hq

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.HeadWindowBooleanRange.ProgramRangeProof
