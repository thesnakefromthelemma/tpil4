/- Constructive -/
namespace ex01

def fp_style : {α : Sort u} → {r : Prop} → (∃ _ : α, r) → r
:=
  fun (Exists.intro _ hr) => hr

end ex01


/- Constructive -/
namespace ex02

def fp_style : {α : Sort u} → {r : Prop} → (a : α) → r → (∃ _ : α, r) :=
Exists.intro

end ex02


/- Constructive -/
namespace ex03

def fp_style : {α : Sort u} → {p : α → Prop} → {r : Prop} → (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (fun (Exists.intro x (And.intro hpx hr)) =>
      And.intro (Exists.intro x hpx) (hr))
    (fun (And.intro (Exists.intro x hpx) hr) =>
      Exists.intro x (And.intro hpx hr))

end ex03


/- Constructive -/
namespace ex04

def fp_style : {α : Sort u} → {p q : α → Prop} → (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun
    | Exists.intro x (Or.inl hpx) => Or.inl (Exists.intro x hpx)
    | Exists.intro x (Or.inr hqx) => Or.inr (Exists.intro x hqx))
    (fun
    | Or.inl (Exists.intro x hpx) => Exists.intro x (Or.inl (hpx))
    | Or.inr (Exists.intro x hqx) => Exists.intro x (Or.inr (hqx)))

end ex04


/- Classical -/
namespace ex05

def fp_style : {α : Sort u} → {p : α → Prop} → (∀ x, p x) ↔ ¬(∃ x, ¬ p x) :=
  sorry

end ex05


/- Classical -/
namespace ex06

def fp_style : {α : Sort u} → {p : α → Prop} → (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  sorry

end ex06


/- Ex07 deferred until after Ex09 (of which it's a special case) -/


/- Classical -/
namespace ex08

def fp_style : {α : Sort u} → {p : α → Prop} → (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  sorry

end ex08


/- Constructive -/
namespace ex09

def fp_style : {α : Sort u} → {p : α → Prop} → {r : Prop} → (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (fun haxipxr (Exists.intro x hpx) => haxipxr x hpx)
    (fun hiepr x hpx => hiepr (Exists.intro x hpx))

end ex09


/- Constructive -/
namespace ex07

def fp_style : {α : Sort u} → {p : α → Prop} → (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  (fun (Iff.intro hl hr) => Iff.intro hr hl) ex09.fp_style

end ex07


/- Classical -/
namespace ex10

def fp_style : {α : Sort u} → {p : α → Prop} → {r : Prop} → (a : α) → (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  sorry

end ex10


/- Classical -/
namespace ex11

def fp_style : {α : Sort u} → {p : α → Prop} → {r : Prop} → (a : α) → (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  fun a =>
    Iff.intro
      (fun (Exists.intro x hirpx) hr => Exists.intro x (hirpx hr))
      (fun hirep => Classical.byCases
        (fun hr => match hirep hr with
        | Exists.intro x hpx => Exists.intro x (fun _ => hpx))
        (fun hnr => Exists.intro a (fun hr => nomatch hnr hr)))

end ex11


/- Constructive -/
namespace ex12

def fp_style : {α : Sort u} → {p q : α → Prop} → (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (fun haxapxqx => And.intro
      (fun x => And.left (haxapxqx x))
      (fun x => And.right (haxapxqx x)))
    (fun (And.intro hap haq) x => And.intro (hap x) (haq x))

end ex12


/- Constructive -/
namespace ex13

def fp_style : {α : Sort u} → {p q : α → Prop} → (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun haxipxqx hap x => (haxipxqx x) (hap x)

end ex13


/- Constructive -/
namespace ex14

def fp_style : {α : Sort u} → {p q : α → Prop} → (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun
  | (Or.inl hap), x => Or.inl (hap x)
  | (Or.inr haq), x => Or.inr (haq x)

end ex14


/- Constructive -/
namespace ex15

def fp_style : {α : Sort u} → {r : Prop} → α → ((∀ x : α, r) ↔ r) :=
  fun a =>
    Iff.intro
      (fun har => har a)
      (fun hr _ => hr)

end ex15


/- Classical -/
namespace ex16

def fp_style : {α : Sort u} → {p : α → Prop} → {r : Prop} → (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  sorry

end ex16


/- Classical -/
namespace ex17

def fp_style : {α : Sort u} → {p : α → Prop} → {r : Prop} → (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (fun haxirpx hr x => (haxirpx x) hr)
    (fun hirap x hr => (hirap hr) x)

end ex17


/- Constructive -/
namespace ex18

def fp_style {men : Sort u} (barber : men) {shaves : men → men → Prop} :
  ¬(∀ x : men, shaves barber x ↔ ¬shaves x x)
:=
  fun hbad => match hbad barber with
    | Iff.intro (hisbbnsbb) (hinsbbsbb) => (fun hnp => hnp (hinsbbsbb hnp)) (fun hp => hisbbnsbb hp hp) -- Y combinator!

end ex18


namespace ex19

def even : Nat → Prop :=
  sorry

end ex19


namespace ex20

def prime : Nat → Prop :=
  sorry

end ex20


namespace ex21

def infinitely_many_primes : Prop :=
  sorry

end ex21


namespace ex22

def Fermat_prime : Nat → Prop :=
  sorry

end ex22


namespace ex23

def infinitely_many_Fermat_primes : Prop :=
  sorry

end ex23


namespace ex24

def goldbach_conjecture : Prop :=
  sorry

end ex24


namespace ex25

def Goldbach's_weak_conjecture : Prop :=
  sorry

end ex25


namespace ex26

def Fermat's_last_theorem : Prop :=
  sorry

end ex26
