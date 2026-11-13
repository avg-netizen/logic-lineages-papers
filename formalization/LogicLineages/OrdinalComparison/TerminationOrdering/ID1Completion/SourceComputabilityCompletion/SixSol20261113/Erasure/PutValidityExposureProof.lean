module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityExposureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof
open OriginalRawSyntaxTransportInternalConstructorSubstitutionProof
open OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open OriginalTypedDecoderInternalScalarProof (pairLeftValue pairRightValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def nilAt : Program 2 := pairOf (constant 2 6) (constant 2 0)
def fields : Fin 6 → Program 2 :=
  ![.projection 1,leftOf (rightOf (rightOf (.projection 0))),leftOf (.projection 0),
    rightOf (rightOf (rightOf (.projection 0))),constant 2 0,nilAt]
def rawResult : Program 2 := pairOf (constant 2 5)
  (pairOf (fields 0) (pairOf (fields 1) (pairOf (fields 2)
    (pairOf (fields 3) (pairOf (fields 4) (fields 5))))))

theorem nilSubstitution : Substitutes (Fin.elim0 : Fin 0 → Program 2) nilConstructor nilAt :=
  pairSubstitution (constantSubstitution Fin.elim0 6) (constantSubstitution Fin.elim0 0)

theorem resultSubstitution : Substitutes fields numberedConstructor rawResult :=
  pairSubstitution (constantSubstitution fields 5)
    (pairSubstitution (Substitutes.projection 0) (pairSubstitution (Substitutes.projection 1)
      (pairSubstitution (Substitutes.projection 2) (pairSubstitution (Substitutes.projection 3)
        (pairSubstitution (Substitutes.projection 4) (Substitutes.projection 5))))))

theorem fieldValues (s typ raw head base label nil : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hn : Nonempty (Derivation body Delta (graph2 nilAt nil s label))) :
    ∀ i, Nonempty (Derivation body Delta
      (programGraph (fields i) (![label,head,typ,base,numeral 0,nil] i) ![s,label])) := by
  let xs : Fin 2 → OTerm alpha := ![s,label]
  have hr := pairRightValue (.projection 0) s typ raw xs (projectionValue 0 xs) hp
  have ht := pairLeftValue (.projection 0) s typ raw xs (projectionValue 0 xs) hp
  have hh := ordinaryHead (rightOf (.projection 0)) raw head base xs hr ho
  have hb := ordinaryBase (rightOf (.projection 0)) raw head base xs hr ho
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases hh (Fin.cases ht
    (Fin.cases hb (Fin.cases (constantValue 0 xs) (Fin.cases hn (fun k => Fin.elim0 k)))))) i

theorem exposure (s t typ raw head base label : OTerm alpha) (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (target nil : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph2 InternalPairing.pairing (t.relabel j) (typ.relabel j) target)) →
      Nonempty (Derivation body Theta (programGraph nilConstructor nil Fin.elim0)) →
      Nonempty (Derivation body Theta (programGraph numberedConstructor target
        ![label.relabel j,head.relabel j,typ.relabel j,base.relabel j,numeral 0,nil])) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programsCases (![rawResult,nilAt] : Fin 2 → Program 2) ![s,label] psi
  intro beta j Theta ys hj hs
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,emptyRename] at hs
  let xs : Fin 2 → OTerm beta := ![s.relabel j,label.relabel j]
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph2Rename] at hp' ho' hr'
  have hn : Nonempty (Derivation body Theta (graph2 nilAt (ys 1) (s.relabel j) (label.relabel j))) := hs 1
  have ht := pairLeftValue (.projection 0) (s.relabel j) (typ.relabel j) (raw.relabel j)
    xs (projectionValue 0 xs) hp'
  have hout := binaryRecover InternalPairing.pairing (leftOf (.projection 0)) rawResult
    (t.relabel j) (typ.relabel j) (ys 0) xs hr' ht (hs 0)
  have hnil := (substitutionGraph nilSubstitution Fin.elim0 xs (ys 1)
    (fun i => Fin.elim0 i)).mpr hn
  have hnumbered := (substitutionGraph resultSubstitution
    ![label.relabel j,head.relabel j,typ.relabel j,base.relabel j,numeral 0,ys 1]
    xs (ys 0) (fieldValues (s.relabel j) (typ.relabel j) (raw.relabel j)
      (head.relabel j) (base.relabel j) (label.relabel j) (ys 1) hp' ho' hn)).mpr (hs 0)
  exact next beta j Theta (ys 0) (ys 1) hj hout hnil hnumbered
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityExposureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityExposureProof
