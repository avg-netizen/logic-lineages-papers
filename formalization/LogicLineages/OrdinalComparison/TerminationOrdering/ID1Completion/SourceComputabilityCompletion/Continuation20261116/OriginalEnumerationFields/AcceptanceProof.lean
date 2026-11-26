module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.MalformedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeBoundsRecursion.CasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalApplicationStepPeelSupportProof (queryCases)
open InputProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem validFromFields (n : Nat) (xs : Fin 6 → OTerm alpha)
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0))) := by
  apply OriginalCodeBoundsRecursion.CasesProof.guardCases n (xs 0) _
  · intro beta j Theta hj hg
    have hfj := renameInto hf j Theta hj
    simp only [programRename,sucRelabel,zRelabel] at hfj
    have hz := MalformedProof.atInput n (fun i => (xs i).relabel j) hg
    obtain ⟨he⟩ := valueUnique (fields n) (suc z) z (fun i => (xs i).relabel j) hfj hz
    exact ⟨Derivation.explosion (sucNeZeroApply he)⟩
  · intro beta j Theta hj hg
    simpa only [graph1Rename,sucRelabel,zRelabel] using hg

theorem forward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param answers : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (ha : Nonempty (Derivation body Delta (graph2 (Equation.answers n) answers key param)))
    (hf : Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs))) :
    Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param)) := by
  have hg := validFromFields n xs hf
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have he := extractFromFields n xs key param (suc z) hk hp hf
  have hl := (Equation.Proof.exchangeEquation n body alpha Delta key param answers (suc z) ha).mp he
  exact LayerAcceptanceProof.positiveRecover n key (xs 0) (xs 1) answers param (suc z) hpair hg hl

theorem backward (n : Nat) (xs : Fin 6 → OTerm alpha) (key param answers : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (ha : Nonempty (Derivation body Delta (graph2 (Equation.answers n) answers key param)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) (xs 0))))
    (hc : Nonempty (Derivation body Delta (graph3 (choose n) (suc z) key answers param))) :
    Nonempty (Derivation body Delta (programGraph (fields n) (suc z) xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  have hl := LayerAcceptanceProof.positiveValue n key (xs 0) (xs 1) answers param (suc z) hpair hg hc
  have he := (Equation.Proof.exchangeEquation n body alpha Delta key param answers (suc z) ha).mpr hl
  exact fieldsFromExtract n xs key param (suc z) hk hp he

def queries (n : Nat) : Fin 3 → Program 6 :=
  ![keyQuery,parameterQuery,.composition (Equation.answers n) ![keyQuery,parameterQuery] ]

theorem cases (n : Nat) (xs : Fin 6 → OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (key param answers : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (programGraph keyQuery key (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Theta (programGraph parameterQuery param (fun i => (xs i).relabel j))) →
      Nonempty (Derivation body Theta (graph2 (Equation.answers n) answers key param)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply queryCases (queries n) xs psi
  intro beta j ys Theta hj hq
  have hk : Nonempty (Derivation body Theta (programGraph keyQuery (ys 0) (fun i => (xs i).relabel j))) := by
    simpa [queries] using hq 0
  have hp : Nonempty (Derivation body Theta (programGraph parameterQuery (ys 1) (fun i => (xs i).relabel j))) := by
    simpa [queries] using hq 1
  have ha : Nonempty (Derivation body Theta (programGraph (.composition (Equation.answers n) ![keyQuery,parameterQuery]) (ys 2) (fun i => (xs i).relabel j))) := by
    simpa [queries] using hq 2
  have har := binaryRecover (Equation.answers n) keyQuery parameterQuery (ys 2) (ys 0) (ys 1)
    (fun i => (xs i).relabel j) ha hk hp
  exact next beta j Theta (ys 0) (ys 1) (ys 2) hj hk hp har
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
