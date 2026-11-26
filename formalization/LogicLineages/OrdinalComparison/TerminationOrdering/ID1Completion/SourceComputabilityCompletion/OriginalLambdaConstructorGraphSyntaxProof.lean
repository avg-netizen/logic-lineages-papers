module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open OriginalLambdaConstructor InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem oneTermEq {alpha : Type} : (numeral 1 : OTerm alpha) = suc z := rfl

@[simp] theorem oneRename {alpha beta : Type} (j : alpha → beta) :
    (numeral 1 : OTerm alpha).relabel j = numeral 1 := by
  simp only [oneTermEq,sucRelabel,zRelabel]

@[simp] theorem fieldsRename {alpha beta : Type}
    (out d e b arrowCode : OTerm alpha) (j : alpha → beta) :
    (Fields out d e b arrowCode).relabel j =
      Fields (out.relabel j) (d.relabel j) (e.relabel j) (b.relabel j) (arrowCode.relabel j) := by
  simp only [Fields,conjunctionRename,graph1Rename,graph2Rename,oneRename]

theorem andIntro {p q : Formula alpha}
    (hp : Nonempty (Derivation body Delta p)) (hq : Nonempty (Derivation body Delta q)) :
    Nonempty (Derivation body Delta (p ⊓ q)) := by
  obtain ⟨hp⟩ := hp
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.conjunctionIntroduction hp hq⟩

theorem andLeft {p q : Formula alpha} (h : Nonempty (Derivation body Delta (p ⊓ q))) :
    Nonempty (Derivation body Delta p) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionLeft h⟩

theorem andRight {p q : Formula alpha} (h : Nonempty (Derivation body Delta (p ⊓ q))) :
    Nonempty (Derivation body Delta q) := by
  obtain ⟨h⟩ := h
  exact ⟨Derivation.conjunctionRight h⟩

/-- Simultaneous witnesses are eliminated inside the original calculus.
This is only original Program totality and composition elimination. -/
theorem queryCases {m n : Nat} (qs : Fin n → Program m) (xs : Fin m → OTerm alpha)
    (psi : Formula alpha)
    (h : ∀ (beta : Type) (j : alpha → beta) (ys : Fin n → OTerm beta) (Theta : List (Formula beta)),
      (∀ r ∈ Delta, r.relabel j ∈ Theta) →
      (∀ i, Nonempty (Derivation body Theta
        (programGraph (qs i) (ys i) (fun a => (xs a).relabel j)))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply programCases (.composition (InternalAcceptance.constantZero n) qs) xs _
  intro beta j Theta v hj hv
  apply programCompositionCases (InternalAcceptance.constantZero n) qs v
    (fun a => (xs a).relabel j) _ hv
  intro gamma k ys Xi hk _ hg
  have hm : ∀ r ∈ Delta, r.relabel (k ∘ j) ∈ Xi := by
    intro r hr
    simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using hk (r.relabel j) (hj r hr)
  have hg' : ∀ i, Nonempty (Derivation body Xi
      (programGraph (qs i) (ys i) (fun a => (xs a).relabel (k ∘ j)))) := by
    intro i
    simpa only [Term.relabel_relabel] using hg i
  simpa only [InternalPositiveUnfoldingSupportProof.formulaRelabelComposition] using h gamma (k ∘ j) ys Xi hm hg'

theorem constructorComponents (d e b payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload b))) :
    ∀ i : Fin 3, Nonempty (Derivation body Delta
      (programGraph ((![Program.projection 0,.projection 1,rightOf (.projection 2)] : Fin 3 → Program 3) i)
        (![d,e,payload] i) (Fin.cons d (Fin.cons e (Fin.cons b Fin.elim0))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons b Fin.elim0))
  intro i
  exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
    (Fin.cases (unaryValue InternalUnpair.right (.projection 2) payload b xs hp
      (projectionValue 2 xs)) (fun q => Fin.elim0 q))) i

theorem constructorForward (out d e b payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload b)))
    (hc : Nonempty (Derivation body Delta (graph3 constructor out d e b))) :
    Nonempty (Derivation body Delta (graph3 packedLambda out d e payload)) :=
  compositionRecover packedLambda ![.projection 0,.projection 1,rightOf (.projection 2)] out
    (Fin.cons d (Fin.cons e (Fin.cons b Fin.elim0)))
    (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) hc
    (constructorComponents d e b payload hp)

theorem constructorBackward (out d e b payload : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload b)))
    (hc : Nonempty (Derivation body Delta (graph3 packedLambda out d e payload))) :
    Nonempty (Derivation body Delta (graph3 constructor out d e b)) :=
  compositionValue packedLambda ![.projection 0,.projection 1,rightOf (.projection 2)] out
    (Fin.cons d (Fin.cons e (Fin.cons b Fin.elim0)))
    (Fin.cons d (Fin.cons e (Fin.cons payload Fin.elim0))) hc
    (constructorComponents d e b payload hp)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
