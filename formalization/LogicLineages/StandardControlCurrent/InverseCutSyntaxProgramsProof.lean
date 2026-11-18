module
public import LogicLineages.StandardControlCurrent.InverseCutSyntaxProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InverseCutSyntaxProof
open InverseCutSyntax

theorem numeralCodeP {α : Type} [Primcodable α] {n : α → Nat}
    (hn : Primrec n) : Primrec (fun x => numeralCode (n x)) :=
  (Primrec.nat_mul.comp (Primrec.const 10) hn)

theorem addCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => addCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) (Primrec₂.natPair.comp ha hb)) (Primrec.const 2))

theorem subCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => subCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) (Primrec₂.natPair.comp ha hb)) (Primrec.const 3))

theorem mulCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => mulCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) (Primrec₂.natPair.comp ha hb)) (Primrec.const 4))

theorem divCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => divCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) (Primrec₂.natPair.comp ha hb)) (Primrec.const 5))

theorem applyCodeP {α : Type} [Primcodable α] {h a : α → Nat}
    (hh : Primrec h) (ha : Primrec a) : Primrec (fun x => applyCode (h x) (a x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) ha) (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) (Primrec.const 6) (Primrec.const 7)))

theorem inverseCodeP {α : Type} [Primcodable α] {h a : α → Nat}
    (hh : Primrec h) (ha : Primrec a) : Primrec (fun x => inverseCode (h x) (a x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10) ha) (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) (Primrec.const 8) (Primrec.const 9)))

theorem lessCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => lessCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp ha hb)) (Primrec.const 3))

theorem andCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => andCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp ha hb)) (Primrec.const 6))

theorem orCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => orCode (a x) (b x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp ha hb)) (Primrec.const 7))

theorem negCodeP {α : Type} [Primcodable α] {a : α → Nat}
    (ha : Primrec a) : Primrec (fun x => negCode (a x)) :=
  (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) ha) (Primrec.const 5))

theorem leCodeP {α : Type} [Primcodable α] {a b : α → Nat}
    (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => leCode (a x) (b x)) :=
  (negCodeP (lessCodeP hb ha))

theorem remainderCodeP {α : Type} [Primcodable α] {m a : α → Nat}
    (hm : Primrec m) (ha : Primrec a) : Primrec (fun x => remainderCode (m x) (a x)) :=
  (subCodeP ha (mulCodeP hm (divCodeP hm ha)))

theorem nextCodeP {α : Type} [Primcodable α] {m r a : α → Nat}
    (hm : Primrec m) (hr : Primrec r) (ha : Primrec a) : Primrec (fun x => nextCode (m x) (r x) (a x)) :=
  (addCodeP ha (remainderCodeP hm (subCodeP (numeralCodeP (Primrec.nat_add.comp hr hm)) (remainderCodeP hm ha))))

theorem branchCodeP {α : Type} [Primcodable α] {h m r a b hi lower : α → Nat}
    (hh : Primrec h) (hm : Primrec m) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) (hhi : Primrec hi) (hlower : Primrec lower) : Primrec (fun x => branchCode (h x) (m x) (r x) (a x) (b x) (hi x) (lower x)) :=
  (orCodeP (andCodeP (leCodeP hlower ha) (andCodeP (leCodeP (nextCodeP hm hr ha) hb) (leCodeP (applyCodeP hh (nextCodeP hm hr ha)) hhi))) (andCodeP (lessCodeP ha hlower) (andCodeP (leCodeP (nextCodeP hm hr hlower) hb) (leCodeP (applyCodeP hh (nextCodeP hm hr hlower)) hhi))))

theorem compileCodeP {α : Type} [Primcodable α] {h m r a b lo hi : α → Nat}
    (hh : Primrec h) (hm : Primrec m) (hr : Primrec r) (ha : Primrec a) (hb : Primrec b) (hlo : Primrec lo) (hhi : Primrec hi) : Primrec (fun x => compileCode (h x) (m x) (r x) (a x) (b x) (lo x) (hi x)) :=
  (Primrec.ite ((Primrec.nat_lt.comp (Primrec.const 0) hm).and (Primrec.nat_lt.comp hr hm)) (orCodeP (andCodeP (leCodeP hlo (applyCodeP hh (numeralCodeP (Primrec.const 0)))) (branchCodeP hh hm hr ha hb hhi (numeralCodeP (Primrec.const 0)))) (andCodeP (lessCodeP (applyCodeP hh (numeralCodeP (Primrec.const 0))) hlo) (branchCodeP hh hm hr ha hb hhi (addCodeP (inverseCodeP hh (subCodeP hlo (numeralCodeP (Primrec.const 1)))) (numeralCodeP (Primrec.const 1)))))) (Primrec.const 1))

theorem syntaxPrograms : InverseCutSyntaxTargets.Programs := by
  have hh : Primrec (fun p : Input => p.1) := (Primrec.fst.comp Primrec.id)
  have hm : Primrec (fun p : Input => p.2.1) := (Primrec.fst.comp (Primrec.snd.comp Primrec.id))
  have hr : Primrec (fun p : Input => p.2.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))
  have ha : Primrec (fun p : Input => p.2.2.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  have hb : Primrec (fun p : Input => p.2.2.2.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id)))))
  have hlo : Primrec (fun p : Input => p.2.2.2.2.2.1) := (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))
  have hhi : Primrec (fun p : Input => p.2.2.2.2.2.2) := (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))))
  exact compileCodeP hh hm hr ha hb hlo hhi

theorem fullSyntax : InverseCutSyntaxTargets.Full :=
  ⟨parameterElimination, outputSupport, updateAndNegation, literalCode, syntaxPrograms, invalid⟩
end LogicLineages.StandardControlCurrent.InverseCutSyntaxProof
