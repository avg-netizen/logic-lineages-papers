module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnaryInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnarySourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality CurrentImplicationCertificate
open SixSol20261112.Fuel NamedArithmeticGraph HistoryCodec.ArithmeticSupport
open GorbowPublishedDCB
theorem exactUnaryRule : Targets.InternalUnaryRule := by
 intro installed lhs rhs k t old a baseX pF pR I n inputs e f ctx G raw left right index fuel
 dsimp only
 intro hraw hl hr
 let p := CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX
 let T := GorbowPRNumeralCalculation.Theory p
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let V := RawReflexivityDispatcher.valid (ctx := ctx) I.previous.current.vtag
 let Gamma := V left :: V right :: List.ofFn (fun i => V (raw.get i))
 have hleft : Nonempty (Hilbert.Local T ctx Gamma (V left)) := ⟨.hypothesis List.mem_cons_self⟩
 have hright : Nonempty (Hilbert.Local T ctx Gamma (V right)) :=
  ⟨.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
 have hrawT : ∀ i, Nonempty (Hilbert.Local T ctx Gamma (V (raw.get i))) := by
  intro i
  exact ⟨.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_ofFn.mpr ⟨i,rfl⟩)))⟩
 have hout := UnaryInternalProof.internal p installed lhs rhs t old a _ I Gamma e f raw left right index fuel hrawT hleft hright
 have hG : ∀ psi, psi ∈ Gamma → Nonempty (Hilbert.Local U ctx G psi) := by
  intro psi hmem
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hl
  rcases List.mem_cons.mp hmem with he | hmem
  · subst psi
    exact hr
  obtain ⟨i,he⟩ := List.mem_ofFn.mp hmem
  subst psi
  exact hraw i
 exact PrescribedSourceAxiomSpecialization.SourceSupportProof.localCut
  (CumulativePropositionalSource.SeedSourceProof.inclusion installed lhs rhs pF pR old a baseX) hG hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnarySourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentEqualityImplication.UnarySourceProof
