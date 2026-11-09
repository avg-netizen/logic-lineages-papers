module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationEncodedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationWitnessProof
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsProof
open InternalCanonicalQuotientEdgeApplicationLiftSyntaxProof (queries constructorsAtQueries)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open GuardedSourceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Delta : List (Formula α)}

theorem corePremisesRename {β : Type} (data : Data) (oldStep : Program 4) (sigma tau : Ty)
    (x y a certificate out other parameter : OTerm α) (j : α → β) :
    (Application.corePremises data oldStep sigma tau x y a certificate out other parameter).relabel j =
      Application.corePremises data oldStep sigma tau (x.relabel j) (y.relabel j)
        (a.relabel j) (certificate.relabel j) (out.relabel j) (other.relabel j) (parameter.relabel j) := by
  simp only [Application.corePremises,conjunctionRename,SupportProof.typedRename,
    SupportProof.edgeRename,InternalParameterizedCanonicalResultFoldSyntaxProof.applicationGraphRename,numeralRename]

theorem parameterPremisesRename {β : Type} (context : Nat) (data : Data) (oldStep : Program 4)
    (sigma tau : Ty) (x y a certificate out other parameter gammaCode : OTerm α) (j : α → β) :
    (Application.parameterPremises context data oldStep sigma tau
      x y a certificate out other parameter gammaCode).relabel j =
      Application.parameterPremises context data oldStep sigma tau
        (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j)
        (out.relabel j) (other.relabel j) (parameter.relabel j) (gammaCode.relabel j) := by
  simp only [Application.parameterPremises,conjunctionRename,corePremisesRename,
    InternalOriginalUniformApplicationTyping.parameterGraph,graph2Rename,numeralRename]

/-- Six actual original Program queries provide every raw witness. Their
graphs and the original edgeLift output, never standard-natural reflection,
reconstruct the exact supplied output certificate at the same parameter. -/
theorem coreLift (n : Nat) (arity : Fin n → Nat) (base : Data)
    (hc : InternalOriginalUniformDescentSelection.Calibrated n arity base)
    (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool)
    (hS : SubtypeClosed (fun typ => typ ∈ S)) (oldStep : Program 4) (sigma tau : Ty)
    (x y a certificate out other lifted parameter gammaCode : OTerm α)
    (hp : Nonempty (Derivation body Delta
      (Application.liftPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (normalizeData base) oldStep sigma tau x y a certificate out other lifted parameter gammaCode))) :
    Nonempty (Derivation body Delta (edgeAccepted (normalizeData base) oldStep out other lifted parameter)) := by
  apply queryCases queries
    (Fin.cons (numeral (typeNumber sigma)) (Fin.cons (numeral (typeNumber tau))
      (Fin.cons a (Fin.cons certificate Fin.elim0))))
    (edgeAccepted (normalizeData base) oldStep out other lifted parameter)
  intro β j ys Theta hj hq
  rw [SupportProof.edgeRename]
  have hcore := renameInto (andLeft hp) j Theta hj
  rw [parameterPremisesRename] at hcore
  have hlift := renameInto (andRight hp) j Theta hj
  simp only [graph4Rename,numeralRename] at hlift
  simp only [consTermRename,emptyRename,numeralRename] at hq
  have hw := constructorsAtQueries (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (a.relabel j) (certificate.relabel j) ys hq
  have he := edgeLiftForward (numeral (typeNumber sigma)) (numeral (typeNumber tau))
    (a.relabel j) (certificate.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    (lifted.relabel j) hw hlift
  exact ApplicationEncodedProof.encodedLift n arity base hc symbols S table hS oldStep sigma tau
    (x.relabel j) (y.relabel j) (a.relabel j) (certificate.relabel j) (out.relabel j)
    (other.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (lifted.relabel j)
    (parameter.relabel j) (gammaCode.relabel j) hcore (andIntro hw he)

theorem actualOriginalUniformApplicationEdgeLift : ApplicationTargets.ActualOriginalUniformApplicationEdgeLift := by
  intro n arity base hc symbols S table hS oldStep body α Delta sigma tau
    x y a certificate out other lifted parameter gammaCode
  let P := Application.liftPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (normalizeData base) oldStep sigma tau x y a certificate out other lifted parameter gammaCode
  obtain ⟨h⟩ := coreLift (body := body) (Delta := P :: Delta) n arity base hc symbols S table hS
    oldStep sigma tau x y a certificate out other lifted parameter gammaCode
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationWitnessProof
