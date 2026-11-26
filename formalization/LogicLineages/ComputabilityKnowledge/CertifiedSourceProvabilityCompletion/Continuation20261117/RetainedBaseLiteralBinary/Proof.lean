module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.HeaderSource
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.SymbolicProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open SixSol20261112.Fuel NamedArithmeticGraph FixedFormulaSubstitution

theorem exactLiteral : Targets.LiteralCalculation := by
 intro f lhs rhs old a baseX pF0 pR pCK pG c
 dsimp only
 intro hA hbase I carrierTag peelTag baseProducerTag hcarrier hpeel hproducer
 let t := CurrentNamedHeaderCertificate.template
 let pF := RetainedBaseProducerInstallation.selected f lhs rhs t old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let K := tags R.previous
 let U := S pF pR outer
 let J := R.previous.previous.previous.previous.template
 have incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old a baseX
 obtain ⟨hb,hH⟩ := HeaderSource.bridge f lhs rhs t old a baseX pF pR c hA hbase I J
 obtain ⟨cb,hC⟩ := RetainedBaseSourceCalculation.StatementChecks.exactSource f lhs rhs 2 t old a baseX pF0 pR pCK pG c
  hA hbase R carrierTag peelTag baseProducerTag hcarrier hpeel hproducer
 refine ⟨hb+cb,?_⟩
 intro ctx r s fuel hg
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let v := GorbowRegistryTuple.headerTerm 2 0 [r,s]
 obtain ⟨hg⟩ := hg
 obtain ⟨hhb⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd U hb cb fuel
 obtain ⟨hcb⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd U cb hb fuel
 have he : cb+hb=hb+cb := Nat.add_comm _ _
 rw [he] at hcb
 have hh := hH ctx r s fuel ⟨.mp hhb hg⟩
 have hc := hC ctx v fuel ⟨.mp hcb hg⟩
 have H := CurrentRecursionProducerCore.FormulaBridge.originalNodes root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R
 have hl : ∀ G, Nonempty (Hilbert.Local (GorbowPRNumeralCalculation.Theory root) ctx G
  (RawReflexivityDispatcher.valid R.previous.current.vtag (unaryValue K.ctag 5 (CurrentNamedAliasCertificate.headerCode K r s)))) := by
  intro G
  obtain ⟨hv⟩ := CurrentNamedHeaderTransport.ValidityProof.headerValid root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R G r s
  exact PrescribedRuntimeCallCongruence.ConstructorValidityProof.unary root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R.previous G true _ hv
 have hm := fun G => RetainedBaseSourceCalculation.AlgebraProof.rawValid root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R G 6 v
 have hr := fun G => CorrectedAugmentationErasure.AlgebraProof.rawValid root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R G (call 6 (v ::ᵥ nil))
 have hj := RetainedBaseSourceCalculation.AlgebraProof.join root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R U incl
  (unaryValue K.ctag 5 (CurrentNamedAliasCertificate.headerCode K r s))
  (RetainedBaseSourceCalculation.rawCall K 6 v)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (call 6 (v ::ᵥ nil))) _ _ index fuel hl hm hr hh hc
 obtain ⟨hcore⟩ := CurrentStructuralProducerCore.CoreTools.project U _ _ index fuel _ _ hj
 obtain ⟨hraw⟩ := SymbolicProof.raw root K H r s
 obtain ⟨hrawS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨hraw⟩
 obtain ⟨halias⟩ := SymbolicProof.namedAlias pF pR outer r s
 have hnum := HistoryLookup.DestructorProof.unaryCallCongruence K.numeralTag _ _ (Support.equalitySymmetry _ _ halias)
 have happ := HistoryAppend.PositiveProof.binaryCongruence K.atag _ _ _ _
  (Support.equalitySymmetry _ _ hrawS) hnum
 have hf := HistoryAppend.PositiveProof.binaryCongruence K.ctag (Term.numeral 0) (Term.numeral 0) _ _
  (.logical (.reflexive _)) happ
 obtain ⟨hfinal⟩ := PrescribedRuntimeSpecialization.BaseProof.coreTransport U [] R.currentK.coreTag index fuel _ _ _ (.base hf) (.base hcore)
 obtain ⟨hout⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R U incl [] _ _ index fuel hfinal
 exact ⟨hout.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary.Proof
