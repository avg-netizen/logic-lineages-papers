module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.InputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.MalformedProof
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel)
open InputProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem extractZero (n : Nat) (key code bound param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing key code bound)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z code))) :
    Nonempty (Derivation body Delta (graph2 (extract n) z key param)) := by
  apply programCases (Equation.answers n) (Fin.cons key (Fin.cons param Fin.elim0)) _
  intro beta j Theta answers hj ha
  simp only [consTermRename,emptyRename] at ha
  simp only [graph2Rename,zRelabel]
  have hkj := renameInto hk j Theta hj
  have hgj := renameInto hg j Theta hj
  rw [graph2Rename] at hkj
  simp only [graph1Rename,zRelabel] at hgj
  exact (Equation.Proof.exchangeEquation n body beta Theta (key.relabel j) (param.relabel j) answers z ha).mpr
    (LayerGuardProof.zeroValue n (key.relabel j) (code.relabel j) (bound.relabel j) answers (param.relabel j) hkj hgj)

theorem atParameter (n : Nat) (xs : Fin 6 → OTerm alpha) (key param : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hp : Nonempty (Derivation body Delta (programGraph parameterQuery param xs)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z (xs 0)))) :
    Nonempty (Derivation body Delta (programGraph (fields n) z xs)) := by
  have hpair := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) key (xs 0) (xs 1) xs hk
    (projectionValue 0 xs) (projectionValue 1 xs)
  exact fieldsFromExtract n xs key param z hk hp (extractZero n key (xs 0) (xs 1) param hpair hg)

theorem atKey (n : Nat) (xs : Fin 6 → OTerm alpha) (key : OTerm alpha)
    (hk : Nonempty (Derivation body Delta (programGraph keyQuery key xs)))
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z (xs 0)))) :
    Nonempty (Derivation body Delta (programGraph (fields n) z xs)) := by
  apply programCases parameterQuery xs _
  intro beta j Theta param hj hp
  simp only [programRename,zRelabel]
  have hkj := renameInto hk j Theta hj
  have hgj := renameInto hg j Theta hj
  rw [programRename] at hkj
  simp only [graph1Rename,zRelabel] at hgj
  exact atParameter n (fun i => (xs i).relabel j) (key.relabel j) param hkj hp hgj

theorem atInput (n : Nat) (xs : Fin 6 → OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) z (xs 0)))) :
    Nonempty (Derivation body Delta (programGraph (fields n) z xs)) := by
  apply programCases keyQuery xs _
  intro beta j Theta key hj hk
  simp only [programRename,zRelabel]
  have hgj := renameInto hg j Theta hj
  simp only [graph1Rename,zRelabel] at hgj
  exact atKey n (fun i => (xs i).relabel j) key hk hgj

theorem internalMalformed : Targets.InternalMalformed := by
  intro n body alpha Delta raw b S H labels tupleBound hg
  exact atInput n ![raw,b,S,H,labels,tupleBound] hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.MalformedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.MalformedProof
