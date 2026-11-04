module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecSupportProof
open Source QuotientDirectPrimrec QuotientDominationCertificates NumberedQuotientPathCertificates

abbrev Context (n : Nat) := Parameters n × List Nat

theorem optionAnyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → Option B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) :=
  (Primrec.option_casesOn hf (Primrec.const false) hg).of_eq (by intro a; cases f a <;> rfl)

def witness (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (ctx : Context n) (y : Nat) (entry : Entry) : Bool :=
  (ctx.2[entry.1]?).any (fun z => positivePathTest n arity ctx.1.1.1 ctx.1.1.2 Gamma ctx.1.2 z y entry.2)

theorem witnessPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Context n × Nat × Entry => witness n arity Gamma p.1 p.2.1 p.2.2) := by
  apply optionAnyPrimitive (Primrec.list_getElem?.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id)) (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  exact ((NumberedQuotientCertificatesPrimrecProof.positivePathTestPrimitive n arity Gamma).comp
    ((Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id)))).pair ((Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.id)))).pair ((Primrec.snd.comp Primrec.id).pair ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))).pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id))))))))).to₂

def step (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (ctx : Context n) (state : List Nat × Bool) (entry : Entry) : List Nat × Bool :=
  (state.1.tail, state.2 && state.1.head?.any (fun y => witness n arity Gamma ctx y entry))

def finish (state : List Nat × Bool) : Bool := decide (state.1 = []) && state.2

theorem foldCalibration (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (ctx : Context n) (inserted : List Nat) (entries : List Entry) (ok : Bool) :
    finish (entries.foldl (step n arity Gamma ctx) (inserted,ok)) =
      (ok && test n arity ctx.1.1.1 ctx.1.1.2 Gamma ctx.1.2 ctx.2 inserted entries) := by
  induction entries generalizing inserted ok with
  | nil => cases inserted <;> cases ok <;> rfl
  | cons entry entries ih =>
    rcases entry with ⟨index,certificate⟩
    cases inserted with
    | nil => simpa [List.foldl_cons,step,finish,test] using ih [] false
    | cons y ys =>
      simp only [List.foldl_cons,step,List.tail_cons,List.head?_cons,Option.any_some]
      rw [ih]
      cases h : ctx.2[index]? with
      | none => simp [witness,h,test]
      | some z => simp [witness,h,test,Bool.and_assoc]

theorem stepPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : Context n × (List Nat × Bool) × Entry => step n arity Gamma p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : Context n × (List Nat × Bool) × Entry => p.2.1.1.tail) :=
    Primrec.list_tail.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id)))
  have hh : Primrec (fun p : Context n × (List Nat × Bool) × Entry =>
      p.2.1.1.head?.any (fun y => witness n arity Gamma p.1 y p.2.2)) :=
    optionAnyPrimitive (Primrec.list_head?.comp (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))))
      ((witnessPrimitive n arity Gamma).comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.id)).pair ((Primrec.snd.comp Primrec.id).pair (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.id)))))).to₂
  exact ht.pair (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.id))) hh)

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectPrimrecSupportProof
