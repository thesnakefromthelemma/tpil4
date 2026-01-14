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
    (fun hdne =>
      hdne (fun hnopnp =>
        (hnopnp ∘ Or.inr) (hnopnp ∘ Or.inl)))

theorem math_style : ({p : Prop} → p ∨ ¬p) ↔ ({p : Prop} → ¬¬p → p) :=
  have hiopnpinnpp : ({p : Prop} → p ∨ ¬p) → {p : Prop} → ¬¬p → p :=
    fun hem _ hnnp =>
      Or.elim hem
        (fun hp => hp)
        (fun hnp => False.elim (hnnp hnp))
  have hiinnppopnp : ({p : Prop} → ¬¬p → p) → {p : Prop} → p ∨ ¬p :=
    fun hdne =>
      hdne (fun hnopnp =>
        (fun hnp => hnopnp (Or.inr hnp)) (fun hp => hnopnp (Or.inl hp)))
  Iff.intro hiopnpinnpp hiinnppopnp

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
      have hp : p :=
        And.left hapq
      have hq : q :=
        And.right hapq
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
  have hiaapqrapaqr : (p ∧ q) ∧ r → p ∧ (q ∧ r) :=
    fun haapqr =>
      have hapq : p ∧ q :=
        And.left haapqr
      have hp : p :=
        And.left hapq
      have hq : q :=
        And.right hapq
      have hr : r :=
        And.right haapqr
      have haqr : q ∧ r :=
        And.intro hq hr
      And.intro hp haqr
  have hapaqriaapqr : p ∧ (q ∧ r) → (p ∧ q) ∧ r :=
    fun hapaqr =>
      have hp : p :=
        And.left hapaqr
      have haqr : q ∧ r :=
        And.right hapaqr
      have hq : q :=
        And.left haqr
      have hr : r :=
        And.right haqr
      have hapq : p ∧ q :=
        And.intro hp hq
      And.intro hapq hr
  Iff.intro hiaapqrapaqr hapaqriaapqr

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
  have hioopqropoqr : (p ∨ q) ∨ r → p ∨ (q ∨ r) :=
    fun hoopqr => Or.elim hoopqr
      (fun hopq => Or.elim hopq
        (fun hp => Or.inl hp)
        (fun hq => Or.inr (Or.inl hq)))
      (fun hr => Or.intro_right _ (Or.intro_right _ hr))
  have hiopoqroopqr : p ∨ (q ∨ r) → (p ∨ q) ∨ r :=
    fun hopoqr => Or.elim hopoqr
      (fun hp => Or.inl (Or.inl hp))
      (fun hoqr => Or.elim hoqr
        (fun hq => Or.inl (Or.inr hq))
        (fun hr => Or.inr hr))
  Iff.intro hioopqropoqr hiopoqroopqr

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

theorem math_style {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  have hiapoqroapqapr : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
    fun hapoqr =>
      have hp : p :=
        And.left hapoqr
      have hoqr : q ∨ r :=
        And.right hapoqr
      Or.elim hoqr
        (fun hq => Or.inl (And.intro hp hq))
        (fun hr => Or.inr (And.intro hp hr))
  have hioapqaprapoqr : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) :=
    fun hoapqapr => Or.elim hoapqapr
      (fun hapq =>
        have hp : p :=
          And.left hapq
        have hq : q :=
          And.right hapq
        And.intro hp (Or.inl hq))
      (fun hapr =>
        have hp : p :=
          And.left hapr
        have hr : r :=
          And.right hapr
        And.intro hp (Or.inr hr))
  Iff.intro hiapoqroapqapr hioapqaprapoqr

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

theorem math_style {p q r : Prop} : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  have hiopaqraopqopr : p ∨ (q ∧ r) → (p ∨ q) ∧ (p ∨ r) :=
    fun hopaqr => Or.elim hopaqr
      (fun hp => And.intro (Or.inl hp) (Or.inl hp))
      (fun haqr =>
        have hq : q :=
          And.left haqr
        have hr : r :=
          And.right haqr
        And.intro (Or.inr hq) (Or.inr hr))
  have hiaopqopropaqr : (p ∨ q) ∧ (p ∨ r) → p ∨ (q ∧ r) :=
    fun haopqopr =>
      have hopq : p ∨ q :=
        And.left haopqopr
      have hopr : p ∨ r :=
        And.right haopqopr
      Or.elim hopq
        (fun hp => Or.inl hp)
        (fun hq => Or.elim hopr
          (fun hp => Or.inl hp)
          (fun hr => Or.inr (And.intro hq hr)))
  Iff.intro hiopaqraopqopr hiaopqopropaqr

end ex06


/- Constructive Currying -/
namespace ex07

def fp_style : {p q r : Prop} → (p → q → r) ↔ (p ∧ q → r) :=
  Iff.intro
    (fun hipiqr (And.intro hp hq) => hipiqr hp hq)
    (fun hiapqr hp hq => hiapqr (And.intro hp hq))

theorem math_style {p q r : Prop} : (p → q → r) ↔ (p ∧ q → r) :=
  have hiipiqriapqr : (p → q → r) → (p ∧ q → r) :=
    fun hipiqr hapq =>
      have hp : p :=
        And.left hapq
      have hq : q :=
        And.right hapq
      hipiqr hp hq
  have hiiapqripiqr : (p ∧ q → r) → (p → q → r) :=
    fun hiapqr hp hq =>
      hiapqr (And.intro hp hq)
  Iff.intro hiipiqriapqr hiiapqripiqr

end ex07


/- Constructive UP of disjunction -/
namespace ex08

def fp_style : {p q r : Prop} → ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (fun hiopqr =>
      And.intro
        (hiopqr ∘ Or.inl)
        (hiopqr ∘ Or.inr))
    (fun
    | And.intro hipr _, Or.inl hp => hipr hp
    | And.intro _ hiqr, Or.inr hq => hiqr hq)

theorem math_style {p q r : Prop} : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  have hiiopqraipriqr : ((p ∨ q) → r) → (p → r) ∧ (q → r) :=
    fun hiopqr =>
      And.intro
        (fun hp =>
          hiopqr (Or.inl hp))
        (fun hq =>
          hiopqr (Or.inr hq))
  have hiaipriqriopqr : (p → r) ∧ (q → r) → (p ∨ q) → r :=
    fun haipriqr hopq =>
      Or.elim hopq
        (fun hp =>
          have hipr : p → r :=
            And.left haipriqr
          hipr hp)
        (fun hq =>
          have hiqr : q → r :=
            And.right haipriqr
          hiqr hq)
  Iff.intro hiiopqraipriqr hiaipriqriopqr

end ex08


/- Constructive DeMorgan for disjunction -/
namespace ex09

def fp_style : {p q : Prop} → ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (fun hnopq => And.intro
      (hnopq ∘ Or.inl)
      (hnopq ∘ Or.inr))
    (fun (And.intro hnp hnq) => fun
      | Or.inl hp => hnp hp
      | Or.inr hq => hnq hq)

theorem math_style {p q : Prop} : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  have hinopqanpnq : ¬(p ∨ q) → ¬p ∧ ¬q :=
    fun hnopq => And.intro
      (fun hp => hnopq (Or.inl hp))
      (fun hq => hnopq (Or.inr hq))
  have hianpnqnopq : ¬p ∧ ¬q → ¬(p ∨ q) :=
    fun hanpnq hopq =>
      have hnp : ¬p :=
        And.left hanpnq
      have hnq : ¬q :=
        And.right hanpnq
      Or.elim hopq
        (fun hp => hnp hp)
        (fun hq => hnq hq)
  Iff.intro hinopqanpnq hianpnqnopq

end ex09


/- Constructive anti-DeMorgan for conjunction -/
namespace ex10

def fp_style : {p q : Prop} → ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun
  | (Or.inl hnp), (And.intro hp _) => hnp hp
  | (Or.inr hnq), (And.intro _ hq) => hnq hq

theorem math_style {p q : Prop} : ¬p ∨ ¬q → ¬(p ∧ q) :=
  fun honpnq hapq => Or.elim honpnq
    (fun hnp =>
      have hp : p :=
        And.left hapq
      hnp hp)
    (fun hnq =>
      have hq : q :=
        And.right hapq
      hnq hq)

end ex10


/- Constructive inconsistency of inconsistency -/
namespace ex11

def fp_style : {p : Prop} → ¬(p ∧ ¬p) :=
  fun (And.intro hp hnp) =>
    hnp hp

theorem math_style {p : Prop} : ¬(p ∧ ¬p) :=
  fun hapnp =>
    have hp : p :=
      And.left hapnp
    have hnp : ¬p :=
      And.right hapnp
    hnp hp

end ex11


/- Constructive Exercise 12 -/
namespace ex12

def fp_style : {p q : Prop} → p ∧ ¬q → ¬(p → q) :=
  fun (And.intro hp hnq) hipq =>
    hnq (hipq hp)

theorem math_style {p q : Prop} : p ∧ ¬q → ¬(p → q) :=
  fun hapnq hipq =>
    have hp : p :=
      And.left hapnq
    have hnq : ¬q :=
      And.right hapnq
    hnq (hipq hp)

end ex12


/- Constructive Exercise 13 -/
namespace ex13

def fp_style : {p q : Prop} → ¬p → p → q :=
  fun hnp hp =>
    nomatch hnp hp

theorem math_style {p q : Prop} : ¬p → p → q :=
  fun hnp hp =>
    have hf : False :=
      hnp hp
    False.elim hf

end ex13


/- Constructive Exercise 14 -/
namespace ex14

def fp_style : {p q : Prop} → (¬p ∨ q) → p → q :=
  fun
  | (Or.inl hnp), hp => nomatch hnp hp
  | (Or.inr hq), _ => hq

theorem math_style {p q : Prop} : (¬p ∨ q) → p → q :=
  fun honpq hp => Or.elim honpq
    (fun hnp => False.elim (hnp hp))
    (fun hq => hq)

end ex14


/- Constructive Exercise 15 -/
namespace ex15

def fp_style : {p : Prop} → p ∨ False ↔ p :=
  Iff.intro
    (fun
    | Or.inl hp => hp
    | Or.inr hf => nomatch hf)
    (Or.inl)

theorem math_style {p : Prop} : p ∨ False ↔ p :=
  have hiopfp : p ∨ False → p :=
    fun hopf =>
      Or.elim hopf
        (fun hp => hp)
        (fun hf => False.elim hf)
  have hipopf : p → p ∨ False :=
    fun hp =>
      Or.inl hp
  Iff.intro hiopfp hipopf

end ex15


/- Constructive Exercise 16 -/
namespace ex16

def fp_style : {p : Prop} → p ∧ False ↔ False :=
  Iff.intro
    (And.right)
    (fun hf => nomatch hf)

theorem math_style {p : Prop} : p ∧ False ↔ False :=
  have hiapff : p ∧ False → False :=
    And.right
  have hifapf : False → p ∧ False :=
    False.elim
  Iff.intro hiapff hifapf


/- Constructive Exercise 17 -/
namespace ex17

def fp_style : {p q : Prop} → (p → q) → ¬q → ¬p :=
  flip (· ∘ ·)

theorem math_style {p q : Prop} : (p → q) → ¬q → ¬p :=
  fun hipq hnq hp =>
    have hq : q :=
      hipq hp
    hnq hq

end ex17


/- Constructive inconsistency of Liars -/
namespace ex18

def fp_style : {p : Prop} → ¬(p ↔ ¬p) :=
  fun (Iff.intro hipnp hinpp) =>
    (fun hnp => hnp (hinpp hnp)) (fun hp => hipnp hp hp) -- Y combinator!

theorem math_style {p : Prop} : ¬(p ↔ ¬p) :=
  fun hepnp =>
    have hipnp : p → ¬p :=
      Iff.mp hepnp
    have hnp : ¬p :=
      fun hp => hipnp hp hp
    have hinpp : ¬p → p :=
      Iff.mpr hepnp
    have hnnp : ¬¬p :=
      fun hnp => hnp (hinpp hnp)
    hnnp hnp

end ex18

/- Classical Exercise 19 -/
namespace ex19

def fp_style : {p q r : Prop} → (p → q ∨ r) → (p → q) ∨ (p → r) :=
  match Classical.em _ with
  | Or.inl hp =>
      fun hipoqr => match hipoqr hp with
      | Or.inl hq => Or.inl (fun _ => hq)
      | Or.inr hr => Or.inr (fun _ => hr)
  | Or.inr hnp => fun _ =>
      Or.inl (fun hp => nomatch hnp hp)

theorem math_style {p q r : Prop} : (p → q ∨ r) → (p → q) ∨ (p → r) :=
  have hopnp : p ∨ ¬p :=
    Classical.em _
  Or.elim hopnp
    (fun hp => fun hipoqr =>
      have hoqr : q ∨ r :=
        hipoqr hp
      Or.elim hoqr
        (fun hq =>
          have hipq : p → q :=
            fun _ => hq
          Or.inl hipq)
        (fun hr =>
          have hipr : p → r :=
            fun _ => hr
          Or.inr hipr))
    (fun hnp => fun _ =>
      have hipq : p → q :=
        fun hp => False.elim (hnp hp)
      Or.inl hipq)

end ex19


/- Classical Exercise 20 -/
namespace ex20

def fp_style : {p q : Prop} → ¬(p ∧ q) → ¬p ∨ ¬q :=
  match Classical.em _ with
  | Or.inl hp => fun hnaqp =>
      Or.inr (fun hq =>
        hnaqp (And.intro hp hq))
  | Or.inr hnp => fun _ => Or.inl hnp

theorem math_style {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q :=
  have hopnp : p ∨ ¬p :=
    Classical.em _
  Or.elim hopnp
    (fun hp => fun hnapq =>
      have hnq : ¬q :=
        fun hq =>
          have hapq : p ∧ q :=
            And.intro hp hq
          hnapq hapq
      Or.inr hnq)
    (fun hnp => fun _ => Or.inl hnp)

end ex20


/- Classical Exercise 21 -/
namespace ex21

def fp_style : {p q : Prop} → ¬(p → q) → p ∧ ¬q :=
  fun hnipq => And.intro
    (Classical.byContradiction (fun hnp =>
      nomatch hnipq (fun hp => nomatch hnp hp)))
    (fun hq => nomatch hnipq (fun _ => hq))

theorem math_style {p q : Prop} : ¬(p → q) → p ∧ ¬q :=
  fun hnipq =>
    have hnnp : ¬¬p :=
      fun hnp =>
        have hipq : p → q :=
          fun hp => False.elim (hnp hp)
        False.elim (hnipq hipq)
    have hp : p :=
      Classical.byContradiction hnnp
    have hnq : ¬q :=
      fun hq =>
        have hipq : p → q :=
          fun _ => hq
        False.elim (hnipq hipq)
    And.intro hp hnq

end ex21


/- Classical Exercise 22 -/
namespace ex22

def fp_style : {p q : Prop} → (p → q) → ¬p ∨ q :=
  match Classical.em _ with
  | Or.inl hp => fun hipq => Or.inr (hipq hp)
  | Or.inr hnp => fun _ => Or.inl hnp


theorem math_style {p q : Prop} : (p → q) → ¬p ∨ q :=
  have hopnp : p ∨ ¬p :=
    Classical.em _
  Or.elim hopnp
    (fun hp => fun hipq =>
      have hq : q :=
        hipq hp
      Or.inr hq)
    (fun hnp => fun _ => Or.inl hnp)

end ex22


/- Classical Exercise 23 -/
namespace ex23

def fp_style : {p q : Prop} → (¬q → ¬p) → p → q :=
  fun hinqnp hp =>
    Classical.byContradiction (fun hnq =>
      (hinqnp hnq) hp)

theorem math_style {p q : Prop} : (¬q → ¬p) → p → q :=
  fun hinqnp hp =>
    have hnnq : ¬¬q :=
      fun hnq =>
        have hnp : ¬p :=
          hinqnp hnq
        hnp hp
    Classical.byContradiction hnnq

end ex23


/- Classical Exercise 24 -/
namespace ex24

def fp_style : {p : Prop} → p ∨ ¬p :=
  Classical.em _

theorem math_style {p : Prop} : p ∨ ¬p :=
  Classical.em _

end ex24


/- Classical Peirce's law -/
namespace ex25

def fp_style : {p q : Prop} → ((p → q) → p) → p :=
  match Classical.em _ with
  | Or.inl hp => fun _ => hp
  | Or.inr hnp => fun hiipqp => hiipqp (fun hp => nomatch hnp hp)

theorem math_style {p q : Prop} : ((p → q) → p) → p :=
  Or.elim (Classical.em _)
    (fun hp => fun _ => hp)
    (fun hnp => fun hiipqp =>
      have hipq : p → q :=
        fun hp => False.elim (hnp hp)
      hiipqp hipq)

end ex25
