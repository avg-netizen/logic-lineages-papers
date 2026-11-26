module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.EquationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def relation (n : Nat) (raw answers out : OTerm alpha) : Formula alpha :=
  (graph1 (OriginalCodeValidityGuard.check n) z raw ⊓ eqn out z) ⊔
  (graph1 (OriginalCodeValidityGuard.check n) (suc z) raw ⊓
    graph2 (OriginalBoundsRecombination.recombine n) (suc out) raw answers)

theorem relationRename {beta : Type} (n : Nat) (raw answers out : OTerm alpha) (j : alpha → beta) :
    (relation n raw answers out).relabel j = relation n (raw.relabel j) (answers.relabel j) (out.relabel j) := by
  simp only [relation,OriginalCodeValidityConstructors.Proof.disjRename,InternalRecursionGraphStepSyntaxProof.conjunctionRename,
    graph1Rename,graph2Rename,sucRelabel,zRelabel,eqnRelabel]

theorem forward (n : Nat) (raw answers param out : OTerm alpha)
    (ho : Nonempty (Derivation body Delta (graph3 (layer n) (suc out) raw answers param))) :
    Nonempty (Derivation body Delta (relation n raw answers out)) := by
  apply CasesProof.guardCases n raw
  · intro beta j Theta hj hg
    rw [relationRename]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    simp only [graph3Rename,sucRelabel] at hoj
    have hv := SupportProof.zeroValue n (raw.relabel j) (answers.relabel j) (param.relabel j) hg
    obtain ⟨he⟩ := valueUnique (layer n) (suc (out.relabel j)) (suc z)
      ![raw.relabel j,answers.relabel j,param.relabel j] hoj hv
    obtain ⟨hr⟩ := andIntro hg ⟨cancelSuc he⟩
    exact ⟨InternalQuotientComparisonProof.orLeft hr⟩
  · intro beta j Theta hj hg
    rw [relationRename]
    have hoj := InternalGraphCompositionFunctionalityProof.renameInto ho j Theta hj
    simp only [graph3Rename,sucRelabel] at hoj
    have hv := CasesProof.positiveRecover n (raw.relabel j) (answers.relabel j) (param.relabel j)
      (suc (out.relabel j)) hg hoj
    obtain ⟨hr⟩ := andIntro hg hv
    exact ⟨InternalQuotientComparisonProof.orRight hr⟩

theorem backward (n : Nat) (raw answers param out : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (relation n raw answers out))) :
    Nonempty (Derivation body Delta (graph3 (layer n) (suc out) raw answers param)) := by
  let A := graph1 (OriginalCodeValidityGuard.check n) z raw ⊓ eqn out z
  let B := graph1 (OriginalCodeValidityGuard.check n) (suc z) raw ⊓
    graph2 (OriginalBoundsRecombination.recombine n) (suc out) raw answers
  have ha : Nonempty (Derivation body Delta (A.imp (graph3 (layer n) (suc out) raw answers param))) := by
    have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hv := SupportProof.zeroValue n raw answers param (andLeft h)
    obtain ⟨he⟩ := andRight h
    have hs := congSuc he
    obtain ⟨hv⟩ := outputTransport (layer n) (suc z) (suc out) ![raw,answers,param] ⟨symm hs⟩ hv
    exact ⟨Derivation.implicationIntroduction hv⟩
  have hb : Nonempty (Derivation body Delta (B.imp (graph3 (layer n) (suc out) raw answers param))) := by
    have h : Nonempty (Derivation body (B :: Delta) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨hv⟩ := SupportProof.positiveValue n raw answers param (suc out) (andLeft h) (andRight h)
    exact ⟨Derivation.implicationIntroduction hv⟩
  obtain ⟨hr⟩ := hr
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  exact ⟨InternalBetaTotalityProof.disjunctionElimination hr ha hb⟩

theorem internalLayerEquation : Targets.InternalLayerEquation := by
  intro n body alpha Delta raw answers param out
  exact ⟨forward n raw answers param out,backward n raw answers param out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.EquationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.EquationProof
