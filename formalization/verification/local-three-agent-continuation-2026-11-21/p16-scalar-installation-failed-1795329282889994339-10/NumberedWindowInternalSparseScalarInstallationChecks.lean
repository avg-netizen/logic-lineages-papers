module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationRebuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoveredInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge certificate carrier)
open ID1Completion.InternalAccessibilityRulesSyntaxProof (edgeExists)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalCoordinateChecks (exact_CertificateRules exact_DomainRules)
open NumberedWindowInternalSparseCanonicalAddressChecks (exact_AddressScalarCalibration exact_PositiveAddressCarriers)
open NumberedWindowInternalSparseCoveredInstallationChecks (exact_CoveredInstallation)
open NumberedWindowInternalSparseCoveredWindowTargets (coveredWindow)
open NumberedWindowInternalSparseSymmetricExchangeTargets (pairedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseCanonicalAddressTargets (addressScalar)
open NumberedWindowInternalSparseScalarInstallationTargets
attribute [local irreducible] programGraph

theorem exact_ReinstallScalar : ExactReinstallScalar :=
  NumberedWindowInternalSparseScalarInstallationRebuildProof.reinstall

theorem exact_PhysicalEdgeCarriers : ExactPhysicalEdgeCarriers := by
  intro C s baseX baseW root other syntaxProg cv tv j d W X least raw body c α Γ a b
  let i := addressScalar cv tv W least
  let r := addressPositive cv tv raw least
  let S := data i j r d
  let E := edge S false c a b
  let Δ := E :: Γ
  have h : Derivation body Δ (edge S false c a b) := Derivation.hypothesis List.mem_cons_self
  rw [edgeExists] at h
  have both : Nonempty (Derivation body Δ (unary i (suc z) a ⊓ unary i (suc z) b)) := by
    apply Nonempty.map (Derivation.existentialElimination h)
    let tag : α → α ⊕ Fin 1 := Sum.inl
    let w : OTerm (α ⊕ Fin 1) := .var (.inr 0)
    let hyp := certificate S false c (a.relabel tag) (b.relabel tag) w
    let Θ := hyp :: Δ.map weaken
    have accepted := (exact_CertificateRules i j r d false c body _ Θ (a.relabel tag) (b.relabel tag) w).mp
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨acc⟩ := accepted
    obtain ⟨rule⟩ := exact_PositiveAddressCarriers C s baseX baseW root other syntaxProg cv tv body _ Θ
      (a.relabel tag) w (b.relabel tag)
    change Nonempty (Derivation body Θ ((unary i (suc z) a ⊓ unary i (suc z) b).relabel tag))
    simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel]
    exact ⟨Derivation.implicationElimination rule acc⟩
  obtain ⟨both⟩ := both
  obtain ⟨src⟩ := (exact_DomainRules i j r d false c body α Δ a).mpr ⟨Derivation.conjunctionLeft both⟩
  obtain ⟨dst⟩ := (exact_DomainRules i j r d false c body α Δ b).mpr ⟨Derivation.conjunctionRight both⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction src dst)⟩

theorem exact_ScalarInstallation : ExactScalarInstallation := by
  obtain ⟨C,cover,previous⟩ := exact_CoveredInstallation
  refine ⟨C,cover,?_⟩
  intro entries s W valid symmetric covered
  obtain ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,baseW,v,hRoot,hOther,hSyntax,
    hBaseW,hWindow,hBaseX,hX,hLeast,initial,withLeast,chosen,withApplication,
    hCover,hBound,hEndpoints,hEdge,hOrder,hMutual,hEqual,hSame⟩ := previous entries s W valid symmetric covered
  let windowProg := coveredWindow C s baseW
  let X := guardedExchange C s (pairedExchange baseX)
  let least := packedLeastProgram C X windowProg s
  let raw := typedRaw5 root other windowProg syntaxProg
  let newI := addressScalar cv tv windowProg least
  have actual := exact_AddressScalarCalibration s cv tv windowProg least
    withLeast.2.2.1.1 withLeast.2.2.1.2.1 hWindow hLeast
  obtain ⟨selectedA,installed⟩ := exact_ReinstallScalar entries s W valid newI i j cv tv d oldCore raw least v actual withLeast
  exact ⟨i,j,cv,tv,syntaxProg,baseX,d,oldCore,oldLeast,root,other,baseW,v,hRoot,hOther,hSyntax,hBaseW,
    hWindow,hBaseX,hX,hLeast,initial,withLeast,chosen,withApplication,hCover,hBound,hEndpoints,hEdge,
    hOrder,hMutual,hEqual,hSame,actual,selectedA,installed,
    exact_PhysicalEdgeCarriers C s baseX baseW root other syntaxProg cv tv j d⟩

#print axioms exact_ReinstallScalar
#print axioms exact_PhysicalEdgeCarriers
#print axioms exact_ScalarInstallation
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarInstallationChecks
