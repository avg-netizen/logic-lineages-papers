module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.SeedGraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AxiomTrace
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
open CurrentRecursionBaseProgram.GraphPrimitives

theorem rawGraph {arity ctx : Nat} (p : Program arity) (v : List.Vector (Term ctx) 2)
 (ntag : Nat) (hn : (nodes p)[ntag]? = some ⟨1,LiteralNumeralPrefix.numeralCode⟩) (i : Fin 2) :
 Computes p (raw i) v (LiteralNumeralPrefix.numeralCall ntag (v.get i)) :=
 unary p v LiteralNumeralPrefix.numeralCode ntag hn _ _ (projection p v i)

theorem seedGraph {arity ctx : Nat} (p : Program arity) (v : List.Vector (Term ctx) 2)
 (J : CurrentRecursionBaseProgram.Tags) (I : CurrentBasicProducerProgram.Installation p J) :
 Computes p CurrentNamedAliasCertificate.seedProgram v (Term.numeral (PrescribedSourceAxiomSpecialization.seed matrix)) := by
 have hg := CurrentBasicProducerProgram.SeedGraphProof.axiomGraph p v J I _ _
  (constantValue p v (Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowNamedDefiningTheory.functionAlias (2,0)))))
 obtain ⟨he⟩ := CurrentRecursionProducerCore.AxiomTrace.axiomCode p J I.hp I.hc _
  (GorbowNamedDefiningTheory.functionAlias (2,0)) (.logical (.reflexive _))
 intro tag ht
 obtain ⟨h⟩ := hg tag ht
 exact ⟨Logic.trans _ _ _ h he⟩

theorem graph {arity ctx : Nat} (p : Program arity) (v : List.Vector (Term ctx) 2)
 (J : CurrentRecursionBaseProgram.Tags) (I : CurrentBasicProducerProgram.Installation p J) :
 Computes p CurrentNamedAliasCertificate.program v
  (PrescribedSourceAxiomSpecialization.certificate J.mtag J.ctag J.atag J.r13 matrix
   (v.map (LiteralNumeralPrefix.numeralCall J.ntag))) := by
 let nums := v.map (LiteralNumeralPrefix.numeralCall J.ntag)
 have hr : ∀ i, Computes p (raw i) v (nums.get i) := by
  intro i
  simpa only [nums,List.Vector.get_map] using rawGraph p v J.ntag I.hn i
 have htail : ∀ i : Fin 1, Computes p (raw 1) v ((LiteralNumeralPrefix.numeralCall J.ntag (v.get 1) ::ᵥ nil).get i) := by
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact rawGraph p v J.ntag I.hn 1
 have hq1 := quoteGraph p v (.all matrix) (PrescribedRuntimeSpecialization.runtimeEnvironment 1)
  (fun _ => raw 1) (LiteralNumeralPrefix.numeralCall J.ntag (v.get 1) ::ᵥ nil) J.ctag J.atag I.hc I.ha htail
 have hh1 := headGraph p v (.all matrix) Fin.elim0 nil J.ctag J.atag I.hc I.ha (fun i => Fin.elim0 i)
 have hstep1 := allGraph p v J.ctag J.r13 I.hc I.h13 _ _ _ _ hh1 (rawGraph p v J.ntag I.hn 1)
 have hfirst := mpGraph p v J.mtag I.hm _ _ _ _ _ _ hq1 hstep1 (seedGraph p v J I)
 have hq := quoteGraph p v matrix (PrescribedRuntimeSpecialization.runtimeEnvironment 2) raw nums J.ctag J.atag I.hc I.ha hr
 have hh := headGraph p v matrix (fun _ => raw 1) (LiteralNumeralPrefix.numeralCall J.ntag (v.get 1) ::ᵥ nil) J.ctag J.atag I.hc I.ha htail
 have hstep := allGraph p v J.ctag J.r13 I.hc I.h13 _ _ _ _ hh (rawGraph p v J.ntag I.hn 0)
 have hout := mpGraph p v J.mtag I.hm _ _ _ _ _ _ hq hstep hfirst
 have hv : v = v.get 0 ::ᵥ v.get 1 ::ᵥ nil := by
  ext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
   | zero => rfl
   | succ i => exact Fin.elim0 i
 dsimp only [nums] at hout
 rw [hv] at hout ⊢
 simp only [PrescribedSourceAxiomSpecialization.certificate,PrescribedRuntimeSpecialization.certificate,
  UniformRuntimeSpecializationStep.certificate,UniformRuntimeSpecializationStep.body,
  PrescribedRuntimeSpecialization.EnvironmentProof.specializeHead,PrescribedRuntimeSpecialization.value,List.Vector.map_cons,List.Vector.map_nil,
  List.Vector.head_cons,List.Vector.tail_cons] 
 simpa only [CurrentNamedAliasCertificate.program,tailProgram,CurrentRecursionBaseProgram.quote,
  List.Vector.map_cons,List.Vector.map_nil,
  show (1 : Fin 2) = (0 : Fin 1).succ from rfl,List.Vector.get_cons_zero,List.Vector.get_cons_succ]
  using hout
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate.GraphProof
