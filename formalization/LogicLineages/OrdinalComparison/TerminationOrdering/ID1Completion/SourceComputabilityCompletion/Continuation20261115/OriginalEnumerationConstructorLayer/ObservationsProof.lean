module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.WitnessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.ObservationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FrameProof WitnessProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def prefixQueries (n : Nat) : Fin 6 → Program 7 :=
  ![prefix1 n,prefix2 n,prefix3 n,prefix4 n,prefix5 n,prefix6 n]

theorem componentAt (n : Nat) (xs : Fin 7 → OTerm alpha) (ys : Fin 8 → OTerm alpha)
    (hc : Nonempty (Derivation body Delta (Targets.componentGraphs n xs ys))) (i : Fin 8) :
    Nonempty (Derivation body Delta (programGraph (components n i) (ys i) xs)) := by
  fin_cases i
  · exact (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hc)))))))
  · exact (andRight (andLeft (andLeft (andLeft (andLeft (andLeft (andLeft hc)))))))
  · exact (andRight (andLeft (andLeft (andLeft (andLeft (andLeft hc))))))
  · exact (andRight (andLeft (andLeft (andLeft (andLeft hc)))))
  · exact (andRight (andLeft (andLeft (andLeft hc))))
  · exact (andRight (andLeft (andLeft hc)))
  · exact (andRight (andLeft hc))
  · exact (andRight hc)

theorem atComponents (n : Nat) (xs : Fin 7 → OTerm alpha) (ys : Fin 8 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (layer n) out xs)))
    (hc : Nonempty (Derivation body Delta (Targets.componentGraphs n xs ys)))
    (hm : Nonempty (Derivation body Delta (Targets.branchMember ys code))) :
    Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (prefixQueries n) xs _
  intro beta j zs Theta hj hz
  rw [graph2Rename,GuardedSourceSyntaxProof.numeralRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hcj := InternalGraphCompositionFunctionalityProof.renameInto hc j Theta hj
  rw [componentsRename] at hcj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  rw [memberRename] at hmj
  let all : Fin 14 → OTerm beta := ![(ys 0).relabel j,(ys 1).relabel j,(ys 2).relabel j,(ys 3).relabel j,
    (ys 4).relabel j,(ys 5).relabel j,(ys 6).relabel j,(ys 7).relabel j,zs 0,zs 1,zs 2,zs 3,zs 4,zs 5]
  have hq : ∀ i, Nonempty (Derivation body Theta (programGraph (queries n i) (all i) (fun k => (xs k).relabel j))) := by
    intro i
    fin_cases i
    · exact componentAt n _ _ hcj 0
    · exact componentAt n _ _ hcj 1
    · exact componentAt n _ _ hcj 2
    · exact componentAt n _ _ hcj 3
    · exact componentAt n _ _ hcj 4
    · exact componentAt n _ _ hcj 5
    · exact componentAt n _ _ hcj 6
    · exact componentAt n _ _ hcj 7
    · exact hz 0
    · exact hz 1
    · exact hz 2
    · exact hz 3
    · exact hz 4
    · exact hz 5
  have hp : part all = (fun i => (ys i).relabel j) := by
    funext i
    fin_cases i <;> rfl
  have hmAll : Nonempty (Derivation body Theta (Targets.branchMember (part all) (code.relabel j))) := by
    rw [hp]
    exact hmj
  exact MemberProof.backward all (out.relabel j) (code.relabel j)
    (FrameProof.recover n _ all (out.relabel j) hq hgj) hmAll

theorem forward (n : Nat) (xs : Fin 7 → OTerm alpha) (out code : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (programGraph (layer n) out xs)))
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out code))) :
    Nonempty (Derivation body Delta (InternalFiniteBlocks.block (Targets.witnessMatrix n xs code))) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (queries n) xs _
  intro beta j ys Theta hj hy
  rw [witnessRename]
  have hgj := InternalGraphCompositionFunctionalityProof.renameInto hg j Theta hj
  rw [programRename] at hgj
  have hmj := InternalGraphCompositionFunctionalityProof.renameInto hm j Theta hj
  rw [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hmj
  have hf := FrameProof.recover n _ ys (out.relabel j) hy hgj
  have hc := FrameProof.componentRecover n _ ys hy
  exact WitnessProof.introduce n _ (code.relabel j) (part ys)
    (andIntro hc (MemberProof.forward7 ys (out.relabel j) (code.relabel j) hf hmj))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.ObservationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.ObservationsProof
