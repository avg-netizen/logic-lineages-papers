module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathPrimrecSupportProof
open Source NumberedNumericQuotientEdge NumberedQuotientPathCertificates

abbrev Window (n : Nat) := List (Fin n) × List Ty
abbrev Table (n : Nat) := Fin n → Fin n → Bool
abbrev EdgeInput (n : Nat) := Window n × Table n × Nat × Nat × Nat
abbrev PathInput (n : Nat) := Window n × Table n × Nat × Nat × List EdgeEntry

theorem optionAnyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → Option B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) :=
  (Primrec.option_casesOn hf (Primrec.const false) hg).of_eq (by
    intro a; cases f a <;> rfl)

def foldStep {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Table n) (state : Nat × Bool) (entry : EdgeEntry) : Nat × Bool :=
  (entry.1,state.2 && numericEdgeTest n arity symbols S Gamma table state.1 entry.1 entry.2)

def finish (target : Nat) (state : Nat × Bool) : Bool :=
  state.2 && decide (state.1 = target)

theorem foldCalibration (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Table n) (entries : List EdgeEntry) (x y : Nat) (valid : Bool) :
    finish y (entries.foldl (foldStep arity symbols S Gamma table) (x,valid)) =
      (valid && pathTest n arity symbols S Gamma table x y entries) := by
  induction entries generalizing x valid with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨z,certificate⟩
    simp only [List.foldl_cons, foldStep, ih, pathTest, Bool.and_assoc]

attribute [local irreducible] numericEdgeTest pathTest

theorem pathTestPrimitiveOfEdge (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hedge : Primrec (fun p : EdgeInput n =>
      numericEdgeTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Primrec (fun p : PathInput n =>
      pathTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hc : Primrec (fun p : PathInput n × ((Nat × Bool) × EdgeEntry) =>
      numericEdgeTest n arity p.1.1.1 p.1.1.2 Gamma p.1.2.1 p.2.1.1 p.2.2.1 p.2.2.2) :=
    hedge.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
  have hs : Primrec (fun p : PathInput n × ((Nat × Bool) × EdgeEntry) =>
      foldStep arity p.1.1.1 p.1.1.2 Gamma p.1.2.1 p.2.1 p.2.2) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hc)
  have hf : Primrec (fun p : PathInput n =>
      p.2.2.2.2.foldl (foldStep arity p.1.1 p.1.2 Gamma p.2.1) (p.2.2.1,true)) :=
    Primrec.list_foldl (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair (Primrec.const true)) hs.to₂
  have h : Primrec (fun p : PathInput n =>
      finish p.2.2.2.1 (p.2.2.2.2.foldl (foldStep arity p.1.1 p.1.2 Gamma p.2.1)
        (p.2.2.1,true))) :=
    Primrec.and.comp (Primrec.snd.comp hf)
      (Primrec.eq.comp (Primrec.fst.comp hf)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).decide
  exact h.of_eq (by
    intro p
    simpa using foldCalibration n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.2.2 p.2.2.1 p.2.2.2.1 true)

theorem pathCertificateDecoderPrimitive :
    NumberedQuotientCertificatesPrimrecTargets.ActualPathCertificateDecoderPrimitive :=
  Primrec.option_map NumberedListCodecPrimrecProof.decoderPrimitive
    ((Primrec.list_map Primrec.id (Primrec.unpair.comp Primrec.snd).to₂).comp Primrec.snd).to₂

theorem positivePathTestPrimitiveOfPath (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (hpath : Primrec (fun p : PathInput n =>
      pathTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Primrec (fun p : EdgeInput n =>
      positivePathTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  have hp : Primrec (fun p : EdgeInput n × List EdgeEntry =>
      pathTest n arity p.1.1.1 p.1.1.2 Gamma p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.2) :=
    hpath.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
            Primrec.snd))))
  have hbody : Primrec (fun p : EdgeInput n × List EdgeEntry =>
      decide (p.2 ≠ []) && pathTest n arity p.1.1.1 p.1.1.2 Gamma p.1.2.1
        p.1.2.2.1 p.1.2.2.2.1 p.2) :=
    Primrec.and.comp (Primrec.eq.comp Primrec.snd (Primrec.const [])).not.decide hp
  have h := optionAnyPrimitive
    (pathCertificateDecoderPrimitive.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))) hbody.to₂
  apply h.of_eq
  intro p
  cases hd : decodePathCertificate p.2.2.2.2 with
  | none => simp [positivePathTest, hd]
  | some entries => cases entries <;> simp [positivePathTest, hd]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathPrimrecSupportProof
