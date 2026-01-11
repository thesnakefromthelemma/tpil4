/- Constructive equivalence
  of principle of excluded middle
  and double negation elimination
-/
namespace ex00

def fp_style : ({p : Prop} → p ∨ ¬p) ↔ ({p : Prop} → ¬¬p → p) :=
  Iff.intro
    (fun hem {_} hnnp =>
      match hem with
      | Or.inl hp => hp
      | Or.inr hnp => nomatch hnnp hnp)
    (fun hdne => hdne
      (fun hnopnp =>
        (hnopnp ∘ Or.inr) (hnopnp ∘ Or.inl)))

theorem math_style : ({p : Prop} → p ∨ ¬p) ↔ ({p : Prop} → ¬¬p → p) :=
  Iff.intro
    (fun hem _ hnnp =>
      Or.elim hem
        (fun hp => hp)
        (fun hnp => False.elim (hnnp hnp)))
    (fun hdne => hdne
      (fun hnopnp =>
        (hnopnp ∘ Or.inr) (hnopnp ∘ Or.inl)))

end ex00

/- Constructive symmetry of conjunction -/
namespace ex01

def fp_style : {p q : Prop} → p ∧ q ↔ q ∧ p :=
  let one_way : {p q : Prop} → p ∧ q → q ∧ p :=
    fun (And.intro hp hq) => And.intro hq hp
  Iff.intro one_way one_way

theorem math_style {p q : Prop} : p ∧ q ↔ q ∧ p :=
  have one_way {p q : Prop} : p ∧ q → q ∧ p :=
    fun hapq =>
      have hp := And.left hapq
      have hq := And.right hapq
      And.intro hq hp
  Iff.intro one_way one_way

end ex01

/- Constructive symmetry of disjunction -/
namespace ex02

def fp_style : {p q : Prop} → p ∨ q ↔ q ∨ p :=
  let one_way : {p q : Prop} → p ∨ q → q ∨ p :=
    fun
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq
  Iff.intro one_way one_way

theorem math_style {p q : Prop} : p ∨ q ↔ q ∨ p :=
  have one_way {p q : Prop} : p ∨ q → q ∨ p :=
    fun hopq => Or.elim hopq
      (fun hp => Or.inr hp)
      (fun hq => Or.inl hq)
  Iff.intro one_way one_way

end ex02

/- Constructive associativity of conjunction -/
namespace ex03

def fp_style : {p q r : Prop} → (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun (And.intro (And.intro hp hq) hr) => And.intro hp (And.intro hq hr))
    (fun (And.intro hp (And.intro hq hr)) => And.intro (And.intro hp hq) hr)

theorem math_style {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun haapqr =>
      have hapq := And.left haapqr
      have hp := And.left hapq
      have hq := And.right hapq
      have hr := And.right haapqr
      have haqr := And.intro hq hr
      And.intro hp haqr)
    (fun hapaqr =>
      have hp := And.left hapaqr
      have haqr := And.right hapaqr
      have hq := And.left haqr
      have hr := And.right haqr
      have hapq := And.intro hp hq
      And.intro hapq hr)

end ex03

/- Constructive associativity of disjunction -/
namespace ex04

def fp_style : {p q r : Prop} → (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun
    | Or.inl (Or.inl hp) => Or.inl hp
    | Or.inl (Or.inr hq) => Or.inr (Or.inl hq)
    | Or.inr hr => Or.inr (Or.inr hr))
    (fun
    | Or.inl hp => Or.inl (Or.inl hp)
    | Or.inr (Or.inl hq) => Or.inl (Or.inr hq)
    | Or.inr (Or.inr hr) => Or.inr hr)

theorem math_style {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hoopqr => Or.elim hoopqr
      (fun hopq => Or.elim hopq
        (fun hp => Or.inl hp)
        (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.intro_right _ (Or.intro_right _ hr)))
    (fun hopoqr => Or.elim hopoqr
      (fun hp => Or.inl (Or.inl hp))
      (fun hoqr => Or.elim hoqr
        (fun hq => Or.inl (Or.inr hq))
        (fun hr => Or.inr hr)))

end ex04

/- Constructive distributivity of conjunction over disjunction -/
namespace ex05

def fp_style : {p q r : Prop} → p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun
    | And.intro hp (Or.inl hq) => Or.inl (And.intro hp hq)
    | And.intro hp (Or.inr hr) => Or.inr (And.intro hp hr))
    (fun
    | Or.inl (And.intro hp hq) => And.intro hp (Or.inl hq)
    | Or.inr (And.intro hp hr) => And.intro hp (Or.inr hr))

theorem math_style : {p q r : Prop} → p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hapoqr =>
      have hp := And.left hapoqr
      have hoqr := And.right hapoqr
      Or.elim hoqr
        (fun hq => Or.inl (And.intro hp hq))
        (fun hr => Or.inr (And.intro hp hr)))
    (fun hoapqapr => Or.elim hoapqapr
      (fun hapq =>
        have hp := And.left hapq
        have hq := And.right hapq
        And.intro hp (Or.inl hq))
      (fun hapr =>
        have hp := And.left hapr
        have hr := And.right hapr
        And.intro hp (Or.inr hr)))

end ex05

/- Constructive distributivity of disjunction over conjunction -/
namespace ex06

def fp_style : {p q r : Prop} → p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun
    | Or.inl hp => And.intro (Or.inl hp) (Or.inl hp)
    | Or.inr (And.intro hq hr) => And.intro (Or.inr hq) (Or.inr hr))
    (fun
    | And.intro (Or.inl hp) _ => Or.inl hp
    | And.intro _ (Or.inl hp) => Or.inl hp
    | And.intro (Or.inr hq) (Or.inr hr) => Or.inr (And.intro hq hr))

theorem math_style : {p q r : Prop} → p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (fun hopaqr => Or.elim hopaqr
      (fun hp => And.intro (Or.inl hp) (Or.inl hp))
      (fun haqr =>
        have hq := And.left haqr
        have hr := And.right haqr
        And.intro (Or.inr hq) (Or.inr hr)))
    (fun haopqopr =>
      have hopq := And.left haopqopr
      have hopr := And.right haopqopr
      Or.elim hopq
        (fun hp => Or.inl hp)
        (fun hq => Or.elim hopr
          (fun hp => Or.inl hp)
          (fun hr => Or.inr (And.intro hq hr))))

end ex06

/- Constructive Currying -/
namespace ex07
end ex07

/- Constructive UP of disjunction -/
namespace ex08
end ex08

/- Constructive DeMorgan for disjunction -/
namespace ex09
end ex09

/- Constructive anti-DeMorgan for conjunction -/
namespace ex10
end ex10

/- Constructive inconsistency of inconsistency -/
namespace ex11
end ex11

namespace ex12
end ex12

namespace ex13
end ex13

namespace ex14
end ex14

namespace ex15
end ex15

namespace ex16
end ex16

namespace ex17
end ex17

/- Constructive inconsistency of Liars -/
namespace ex18

def fp_style : {p : Prop} → ¬(p ↔ ¬p) :=
  fun (Iff.intro hipnp hinpp) =>
    (fun hnp => hnp (hinpp hnp)) (fun hp => hipnp hp hp) -- Y combinator!

theorem math_style {p : Prop} : ¬(p ↔ ¬p) :=
  fun (Iff.intro hipnp hinpp) =>
    have hnp : ¬p :=
      fun hp => hipnp hp hp
    have hnnp : ¬¬p :=
      fun hnp => hnp (hinpp hnp)
    hnnp hnp

end ex18

namespace ex19
end ex19

namespace ex20
end ex20

namespace ex21
end ex21

namespace ex22
end ex22

namespace ex23
end ex23

namespace ex24
end ex24

namespace ex25
end ex25


/-
-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ False ↔ p := sorry
example : p ∧ False ↔ False := sorry
example : (p → q) → (¬q → ¬p) := sorry

Prove the following identities, replacing the sorry placeholders with actual proofs. These require classical reasoning.

open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry
-/
