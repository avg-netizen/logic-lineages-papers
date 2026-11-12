module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (emb)
open InternalSourceInversionSupportProof (onEquality)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem jobTransport (H : Program 1) (M W : Program 2) (c B old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal old new)))
 (ha : Nonempty (Derivation body Delta (Job H M W c B old))) :
 Nonempty (Derivation body Delta (Job H M W c B new)) := by
 let phi : Formula (Fin 3) := Job H M W (.var 0) (.var 1) (.var 2)
 let xs : Fin 3 → OTerm alpha := ![c,B,old]
 let ys : Fin 3 → OTerm alpha := ![c,B,new]
 have hx : phi.subst (fun i => emb (xs i)) = Job H M W c B old := by
  simp only [phi,jobSubst,Term.subst]; rfl
 have hy : phi.subst (fun i => emb (ys i)) = Job H M W c B new := by
  simp only [phi,jobSubst,Term.subst]; rfl
 have eqs : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · simpa only [xs,ys,Matrix.cons_val_zero,equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) c))
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) B))
  · exact he
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 3 Delta phi
  (fun i => emb (xs i)) (fun i => emb (ys i))
  (fun i => by simpa only [InternalControlGraph.equal,onEquality,emb] using eqs i)
  (by rw [hx]; exact ha)
 rwa [hy] at h
theorem frameTransport (H : Program 1) (M W : Program 2) (c B old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal old new)))
 (ha : Nonempty (Derivation body Delta (Frame H M W c B old))) :
 Nonempty (Derivation body Delta (Frame H M W c B new)) := by
 let phi : Formula (Fin 3) := Frame H M W (.var 0) (.var 1) (.var 2)
 let xs : Fin 3 → OTerm alpha := ![c,B,old]
 let ys : Fin 3 → OTerm alpha := ![c,B,new]
 have hx : phi.subst (fun i => emb (xs i)) = Frame H M W c B old := by
  simp only [phi,frameSubst,Term.subst]; rfl
 have hy : phi.subst (fun i => emb (ys i)) = Frame H M W c B new := by
  simp only [phi,frameSubst,Term.subst]; rfl
 have eqs : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · simpa only [xs,ys,Matrix.cons_val_zero,equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) c))
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) B))
  · exact he
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 3 Delta phi
  (fun i => emb (xs i)) (fun i => emb (ys i))
  (fun i => by simpa only [InternalControlGraph.equal,onEquality,emb] using eqs i)
  (by rw [hx]; exact ha)
 rwa [hy] at h
theorem agendaTransport (H : Program 1) (M W : Program 2) (c B old new : OTerm alpha)
 (he : Nonempty (Derivation body Delta (equal old new)))
 (ha : Nonempty (Derivation body Delta (Agenda H M W c B old))) :
 Nonempty (Derivation body Delta (Agenda H M W c B new)) := by
 let phi : Formula (Fin 3) := Agenda H M W (.var 0) (.var 1) (.var 2)
 let xs : Fin 3 → OTerm alpha := ![c,B,old]
 let ys : Fin 3 → OTerm alpha := ![c,B,new]
 have hx : phi.subst (fun i => emb (xs i)) = Agenda H M W c B old := by
  simp only [phi,agendaSubst,Term.subst]; rfl
 have hy : phi.subst (fun i => emb (ys i)) = Agenda H M W c B new := by
  simp only [phi,agendaSubst,Term.subst]; rfl
 have eqs : ∀ i, Nonempty (Derivation body Delta (equal (xs i) (ys i))) := by
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) i
  · simpa only [xs,ys,Matrix.cons_val_zero,equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) c))
  · simpa only [xs,ys,Matrix.cons_val_zero,Matrix.cons_val_succ,equalEqn] using (Nonempty.intro (InternalTagArithmeticSupportProof.refl (body:=body) (Gamma:=Delta) B))
  · exact he
 have h := InternalGraphCompositionEqualityProof.tupleCongruence body alpha 3 Delta phi
  (fun i => emb (xs i)) (fun i => emb (ys i))
  (fun i => by simpa only [InternalControlGraph.equal,onEquality,emb] using eqs i)
  (by rw [hx]; exact ha)
 rwa [hy] at h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
