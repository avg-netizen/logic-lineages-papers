module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.FrameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
def prefix1 (n : Nat) : Program 7 := join variableBranch lambdas
def prefix2 (n : Nat) : Program 7 := join (prefix1 n) applications
def prefix3 (n : Nat) : Program 7 := join (prefix2 n) bottoms
def prefix4 (n : Nat) : Program 7 := join (prefix3 n) (ordinary n)
def prefix5 (n : Nat) : Program 7 := join (prefix4 n) (numbered n)
def prefix6 (n : Nat) : Program 7 := join (prefix5 n) nils
def queries (n : Nat) : Fin 14 → Program 7 :=
  ![variableBranch,lambdas,applications,bottoms,ordinary n,numbered n,nils,argumentCons,
    prefix1 n,prefix2 n,prefix3 n,prefix4 n,prefix5 n,prefix6 n]
def part {alpha : Type} (ys : Fin 14 → OTerm alpha) : Fin 8 → OTerm alpha :=
  ![ys 0,ys 1,ys 2,ys 3,ys 4,ys 5,ys 6,ys 7]
def facts {alpha : Type} (ys : Fin 14 → OTerm alpha) (out : OTerm alpha) : Formula alpha :=
  graph2 InternalApplicationValidityStackAppend.append (ys 8) (ys 0) (ys 1) ⊓
  graph2 InternalApplicationValidityStackAppend.append (ys 9) (ys 8) (ys 2) ⊓
  graph2 InternalApplicationValidityStackAppend.append (ys 10) (ys 9) (ys 3) ⊓
  graph2 InternalApplicationValidityStackAppend.append (ys 11) (ys 10) (ys 4) ⊓
  graph2 InternalApplicationValidityStackAppend.append (ys 12) (ys 11) (ys 5) ⊓
  graph2 InternalApplicationValidityStackAppend.append (ys 13) (ys 12) (ys 6) ⊓
  graph2 InternalApplicationValidityStackAppend.append (out) (ys 13) (ys 7)

theorem componentRecover (n : Nat) (xs : Fin 7 → OTerm alpha) (ys : Fin 14 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) xs))) :
    Nonempty (Derivation body Delta (Targets.componentGraphs n xs (part ys))) := by
  exact andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (andIntro
    (hq 0) (hq 1)) (hq 2)) (hq 3)) (hq 4)) (hq 5)) (hq 6)) (hq 7)

theorem recover (n : Nat) (xs : Fin 7 → OTerm alpha) (ys : Fin 14 → OTerm alpha) (out : OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) xs)))
    (hg : Nonempty (Derivation body Delta (programGraph (layer n) out xs))) :
    Nonempty (Derivation body Delta (facts ys out)) := by
  have h0 := binaryRecover InternalApplicationValidityStackAppend.append variableBranch lambdas
    (ys 8) (ys 0) (ys 1) xs (hq 8) (hq 0) (hq 1)
  have h1 := binaryRecover InternalApplicationValidityStackAppend.append (prefix1 n) applications
    (ys 9) (ys 8) (ys 2) xs (hq 9) (hq 8) (hq 2)
  have h2 := binaryRecover InternalApplicationValidityStackAppend.append (prefix2 n) bottoms
    (ys 10) (ys 9) (ys 3) xs (hq 10) (hq 9) (hq 3)
  have h3 := binaryRecover InternalApplicationValidityStackAppend.append (prefix3 n) (ordinary n)
    (ys 11) (ys 10) (ys 4) xs (hq 11) (hq 10) (hq 4)
  have h4 := binaryRecover InternalApplicationValidityStackAppend.append (prefix4 n) (numbered n)
    (ys 12) (ys 11) (ys 5) xs (hq 12) (hq 11) (hq 5)
  have h5 := binaryRecover InternalApplicationValidityStackAppend.append (prefix5 n) nils
    (ys 13) (ys 12) (ys 6) xs (hq 13) (hq 12) (hq 6)
  have h6 := binaryRecover InternalApplicationValidityStackAppend.append (prefix6 n) argumentCons
    (out) (ys 13) (ys 7) xs hg (hq 13) (hq 7)
  exact andIntro (andIntro (andIntro (andIntro (andIntro (andIntro (h0) h1) h2) h3) h4) h5) h6
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.FrameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationConstructorLayer.FrameProof
